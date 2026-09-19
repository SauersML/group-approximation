"""Repair research/ nodes landed under the gq schema so bin/cairn check passes.

Rules (text-level edits of frontmatter only):
 R1 claim.requires R: if no route targets the claim, add route <id>-via-prereqs
    (requires R); else give R to every route into it that lacks requires; drop
    the key from the claim.
 R2 route without requires whose target has no claim-level requires: requires: [].
 R3 requires entries naming a route: replace by that route's target claim;
    drop self-targets and duplicates.
 R4 invalidates entries naming a claim C: move to C.refuted_by.
 R5 distinct_from keys naming a route: replace by its target; unknown: drop.
 R6 route keys distinct_from/status: drop (status line kept in body).
 R7 route with no/unknown target: becomes a claim (drop target/requires).
 R8 claim key target: drop.
"""
import os, re, sys, json

REPO = sys.argv[1]
RD = os.path.join(REPO, "research")
ID_RE = re.compile(r"^[a-z0-9][a-z0-9-]{1,63}$")


def split(text):
    if not text.startswith("---\n"):
        return None
    end = text.find("\n---\n", 4)
    if end < 0:
        return None
    return text[4:end].split("\n"), text[end + 5:]


def blocks(lines):
    """[(key, [lines])] top-level key blocks."""
    out = []
    for ln in lines:
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):(.*)$", ln)
        if m:
            out.append([m.group(1), [ln]])
        elif out:
            out[-1][1].append(ln)
        else:
            out.append([None, [ln]])
    return out


def parse_list(bl):
    first = bl[0].split(":", 1)[1].strip()
    if first.startswith("["):
        inner = first.strip("[]").strip()
        return [x.strip().strip("'\"") for x in inner.split(",") if x.strip()]
    return [re.sub(r"^\s*-\s*", "", l).strip().strip("'\"") for l in bl[1:] if l.strip().startswith("-")]


def parse_scalar(bl):
    return bl[0].split(":", 1)[1].strip().strip("'\"")


def parse_map_keys(bl):
    return [re.match(r"^\s+([^:]+):", l).group(1).strip().strip("'\"") for l in bl[1:]
            if re.match(r"^\s+[^\s:][^:]*:", l)]


def mk_list(key, vals):
    if not vals:
        return [f"{key}: []"]
    return [f"{key}:"] + [f"  - {v}" for v in vals]


nodes = {}
for fn in sorted(os.listdir(RD)):
    if not fn.endswith(".md"):
        continue
    p = os.path.join(RD, fn)
    t = open(p, encoding="utf-8").read()
    s = split(t)
    if s is None:
        continue
    fm, body = s
    bl = blocks(fm)
    d = {k: b for k, b in bl if k}
    if "id" not in d or "kind" not in d:
        continue
    nid = parse_scalar(d["id"])
    nodes[nid] = dict(path=p, blocks=bl, body=body, kind=parse_scalar(d["kind"]), changed=False)

def get(n, key):
    for k, b in n["blocks"]:
        if k == key:
            return b
    return None

def setb(n, key, lines, after=None):
    for i, (k, b) in enumerate(n["blocks"]):
        if k == key:
            if lines is None:
                del n["blocks"][i]
            else:
                n["blocks"][i] = [key, lines]
            n["changed"] = True
            return
    if lines is None:
        return
    idx = len(n["blocks"])
    if after:
        for i, (k, b) in enumerate(n["blocks"]):
            if k in after:
                idx = i + 1
    n["blocks"].insert(idx, [key, lines])
    n["changed"] = True

kind = {i: n["kind"] for i, n in nodes.items()}
target = {i: parse_scalar(get(n, "target")) for i, n in nodes.items() if n["kind"] == "route" and get(n, "target")}
log = []

# R7 / R8
for i, n in nodes.items():
    if n["kind"] == "route":
        t = target.get(i)
        if not t or t not in nodes or kind[t] != "claim":
            n["blocks"] = [[k, (["kind: claim"] if k == "kind" else b)] for k, b in n["blocks"]]
            for key in ("target", "requires", "status", "distinct_from"):
                setb(n, key, None)
            n["kind"] = kind[i] = "claim"; n["changed"] = True
            target.pop(i, None)
            log.append(f"R7 {i}: route without a valid target ({t!r}) became a claim")
    else:
        if get(n, "target"):
            setb(n, "target", None); log.append(f"R8 {i}: dropped claim key target")

def resolve_claim(x, self_id=None):
    """map an id meant as a claim to a claim id, or None."""
    if x in kind and kind[x] == "claim":
        return x
    if x in target:
        return target[x]
    return None

routes_into = {}
for r, t in target.items():
    routes_into.setdefault(t, []).append(r)

# R1
def written(i):
    m = re.search(r"\*\*(ESTABLISHED|OPEN|REFUTED|SUPERSEDED|PROVED|CONDITIONAL)", nodes[i]["body"])
    return m.group(1) if m else None
claim_req = {}
for i, n in list(nodes.items()):
    if n["kind"] != "claim":
        continue
    b = get(n, "requires")
    if b is None:
        continue
    claim_req[i] = parse_list(b)
    setb(n, "requires", None)

for i, R in claim_req.items():
    rs = routes_into.get(i, [])
    lacking = [r for r in rs if get(nodes[r], "requires") is None]
    if not rs and written(i) not in ("ESTABLISHED", "PROVED"):
        n = nodes[i]
        n["body"] = ("\nInputs this claim recorded under the older schema (not a proof; "
                     "they do not establish it): " + ", ".join(f"`{q}`" for q in R) + ".\n") + n["body"]
        log.append(f"R1 {i}: written {written(i)}, so its {len(R)} prerequisites went to the body, no route")
    elif not rs:
        rid = (i[:52].rstrip("-") + "-via-prereqs")
        nodes[rid] = dict(path=os.path.join(RD, rid + ".md"), kind="route", changed=True, new=True,
                          blocks=[["rg", ["rg: 2"]], ["id", [f"id: {rid}"]], ["kind", ["kind: route"]],
                                  ["title", [f"title: \"The prerequisites recorded on {i} give it\""]],
                                  ["target", [f"target: {i}"]], ["requires", mk_list("requires", R)]],
                          body=(f"\nThis route records the prerequisites that `{i}` listed in its own frontmatter "
                                "(the older schema kept `requires` on claims). The argument is the one in the "
                                f"body of `{i}`, which uses exactly these inputs.\n"))
        kind[rid] = "route"; target[rid] = i; routes_into.setdefault(i, []).append(rid)
        log.append(f"R1 {i}: new route {rid} with its {len(R)} prerequisites")
    else:
        for r in lacking:
            setb(nodes[r], "requires", mk_list("requires", R), after=("target",))
            log.append(f"R1 {i}: gave its {len(R)} prerequisites to route {r}")
        if not lacking:
            log.append(f"R1 {i}: dropped claim-level requires (routes {rs} carry their own)")

# R2
for r, n in list(nodes.items()):
    if n["kind"] == "route" and get(n, "requires") is None:
        t = target[r]
        if written(t) in ("ESTABLISHED", "PROVED") and written(r) in (None, "ESTABLISHED", "PROVED") and not r.startswith("fix-"):
            setb(n, "requires", ["requires: []"], after=("target",))
            log.append(f"R2 {r}: requires: [] (target {t} is written ESTABLISHED)")
        else:
            n["blocks"] = [[k, (["kind: claim"] if k == "kind" else b)] for k, b in n["blocks"]]
            for key in ("target", "status", "distinct_from"):
                setb(n, key, None)
            n["body"] = f"\nRecorded against `{t}` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `{t}`).\n" + n["body"]
            n["kind"] = kind[r] = "claim"; n["changed"] = True
            target.pop(r, None); routes_into[t].remove(r)
            log.append(f"R2 {r}: route without prerequisites into non-established {t} became an OPEN claim")

# R3
for r, n in nodes.items():
    if n["kind"] != "route":
        continue
    b = get(n, "requires")
    R = parse_list(b)
    out = []
    for q in R:
        c = resolve_claim(q)
        if c is None:
            out.append(q); continue
        if c != q:
            log.append(f"R3 {r}: requires {q} (route) -> its target {c}")
        if c == target.get(r) or c in out:
            if c == target.get(r):
                log.append(f"R3 {r}: dropped its own target from requires")
            continue
        out.append(c)
    if out != R:
        setb(n, "requires", mk_list("requires", out))

# R4, R5, R6
for i, n in list(nodes.items()):
    if n["kind"] == "claim":
        b = get(n, "invalidates")
        if b is not None:
            inv = parse_list(b); keep = []
            for x in inv:
                if kind.get(x) == "claim" and routes_into.get(x):
                    for r in routes_into[x]:
                        if r not in keep:
                            keep.append(r)
                    log.append(f"R4 {i}: invalidates claim {x} -> the routes into it {routes_into[x]}")
                elif kind.get(x) == "claim":
                    c = nodes[x]; rb = get(c, "refuted_by")
                    L = parse_list(rb) if rb else []
                    if i not in L:
                        setb(c, "refuted_by", mk_list("refuted_by", L + [i]), after=("title",))
                    log.append(f"R4 {i}: invalidates claim {x} -> {x}.refuted_by")
                else:
                    keep.append(x)
            setb(n, "invalidates", mk_list("invalidates", keep) if keep else None)
        b = get(n, "distinct_from")
        if b is not None:
            lines = [b[0]]; cur_ok = True
            for l in b[1:]:
                m = re.match(r"^(\s+)([^\s:][^:]*):(.*)$", l)
                if m and len(m.group(1)) <= 2:
                    k = m.group(2).strip().strip("'\"")
                    c = k if kind.get(k) == "claim" else None
                    if c is None or c == i:
                        cur_ok = False; log.append(f"R5 {i}: dropped distinct_from {k}"); continue
                    cur_ok = True
                    if c != k:
                        log.append(f"R5 {i}: distinct_from {k} (route) -> {c}")
                        l = f"{m.group(1)}{c}:{m.group(3)}"
                    lines.append(l)
                elif cur_ok:
                    lines.append(l)
            # merge duplicate keys produced by R5
            seen, merged = set(), [lines[0]]
            skip = False
            for l in lines[1:]:
                m = re.match(r"^(\s{1,2})([^\s:][^:]*):", l)
                if m:
                    k = m.group(2).strip()
                    skip = k in seen; seen.add(k)
                if not skip:
                    merged.append(l)
            setb(n, "distinct_from", merged if len(merged) > 1 else None)
    else:
        for key in ("distinct_from", "status"):
            if get(n, key) is not None:
                setb(n, key, None); log.append(f"R6 {i}: dropped route key {key}")

for i, n in nodes.items():
    if not n["changed"]:
        continue
    fm = [l for k, b in n["blocks"] for l in b]
    open(n["path"], "w", encoding="utf-8").write("---\n" + "\n".join(fm) + "\n---\n" + n["body"])

open(sys.argv[2], "w").write("\n".join(log) + "\n")
print(len(log), "edits;", sum(1 for n in nodes.values() if n["changed"]), "files")
