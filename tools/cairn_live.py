#!/usr/bin/env python3
"""cairn-live: real-time coordination for agents working one Cairn graph.

Cairn itself holds what is *known*: claims, routes, attempts. It says nothing
about what is *happening*: who is on which hole, with which idea, what they
have found in the last ten minutes, what they are stuck on. Its leases are
identity-free and one per node. This tool adds that layer.

The model is an event log, not a lock server.

* Every agent appends typed events (claim, heartbeat, lemma, dead, need,
  spark, verdict, landed, ...) to one JSONL file under Cairn's shared state
  directory. Every worktree in a container sees the same file. Each event has
  a random id, so the log is a grow-only set: merging two logs is a union by
  id, whatever the transport (a shared file, a git ref, a copied file).
* State (active leases, open needs, dead approaches) is folded from the log.
  Nothing else is stored, so the log is also the audit trail and the digest.
* Leases are per APPROACH, not per node. Several agents may work one hole,
  but not with the same idea, not with an idea already recorded as dead, and
  by default not inside the same approach family. Divergence is the rule, not
  a hope.
* The atlas reads the graph and counts approach families around a goal:
  which are saturated, which keep dying, and which have established results
  elsewhere in the graph but none here. Role cards turn that into worker
  briefs, so a "new paradigm" is computed against 25k nodes rather than
  guessed from memory.

Env: CAIRN_AGENT names this agent, CAIRN_WAVE the wave, CAIRN_LIVE overrides
the log directory (default <cairn shared state>/live).
"""

import argparse
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("CAIRN_ROOT") or os.path.dirname(HERE)
os.environ.setdefault("CAIRN_ROOT", ROOT)
sys.path.insert(0, HERE)
import cairn  # noqa: E402  (the vendored CLI, used as a library)

EXIT_OK, EXIT_BLOCKED, EXIT_USAGE = 0, 3, 64
KINDS = ("claim", "heartbeat", "release", "dead", "lemma", "need", "spark",
         "question", "answer", "verdict", "landed", "transfer", "family", "note")
DEFAULT_TTL = 4 * 3600
SHORTHAND = ("lemma", "need", "spark", "dead", "release", "verdict", "landed", "question",
             "answer", "note")
PARADIGMS = os.path.join(HERE, "cairn_live_paradigms.json")
STOP = {"the", "and", "for", "with", "from", "into", "via", "use", "using", "a",
        "an", "of", "on", "in", "to", "by", "as", "at", "is", "are", "be", "that",
        "this", "its", "it", "or", "not", "no", "all", "every", "some", "any"}


# ---------------------------------------------------------------------------
# The log
# ---------------------------------------------------------------------------

def live_dir():
    d = os.environ.get("CAIRN_LIVE") or os.path.join(cairn.shared_dir(), "live")
    os.makedirs(d, exist_ok=True)
    return d


def log_path():
    return os.path.join(live_dir(), "events.jsonl")


def agent_name():
    return os.environ.get("CAIRN_AGENT") or f"anon-{os.getpid()}"


def require_agent():
    """Leases are matched by agent name, so anything that holds or ends one
    needs a stable name, not a per-process default."""
    if not os.environ.get("CAIRN_AGENT"):
        print("set CAIRN_AGENT to a stable name for this agent (leases are matched by it)",
              file=sys.stderr)
        raise SystemExit(EXIT_USAGE)


def wave_name():
    return os.environ.get("CAIRN_WAVE") or "default"


class _Locked:
    def __init__(self, name="events.lock"):
        self.path = os.path.join(live_dir(), name)

    def __enter__(self):
        self.f = open(self.path, "a")
        fcntl.flock(self.f, fcntl.LOCK_EX)
        return self

    def __exit__(self, *exc):
        fcntl.flock(self.f, fcntl.LOCK_UN)
        self.f.close()


def read_events(path=None):
    out = []
    try:
        with open(path or log_path(), encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    e = json.loads(line)
                except json.JSONDecodeError:
                    continue  # a torn tail from a killed writer; never fatal
                if isinstance(e, dict) and e.get("id") and e.get("kind") in KINDS:
                    out.append(e)
    except FileNotFoundError:
        pass
    return out


def append(kind, **fields):
    if kind not in KINDS:
        raise ValueError(f"unknown event kind {kind!r}")
    e = {"id": uuid.uuid4().hex, "ts": round(time.time(), 3),
         "agent": agent_name(), "wave": wave_name(), "kind": kind}
    e.update({k: v for k, v in fields.items() if v not in (None, "", [])})
    with _Locked():
        with open(log_path(), "a", encoding="utf-8") as f:
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    return e


def merge_events(incoming):
    """Append events whose ids are unseen. Existing lines never move, so
    line-number cursors stay valid. Returns the number added."""
    with _Locked():
        seen = {e["id"] for e in read_events()}
        fresh = [e for e in incoming if e.get("id") and e["id"] not in seen
                 and e.get("kind") in KINDS]
        fresh.sort(key=lambda e: e.get("ts", 0))
        if fresh:
            with open(log_path(), "a", encoding="utf-8") as f:
                for e in fresh:
                    f.write(json.dumps(e, ensure_ascii=False) + "\n")
    return len(fresh)


# ---------------------------------------------------------------------------
# Folding the log into state
# ---------------------------------------------------------------------------

def sig_tokens(text):
    return {w for w in re.findall(r"[a-z0-9]+", (text or "").lower())
            if w not in STOP and len(w) > 1}


def same_idea(a, b, threshold=0.6):
    ta, tb = sig_tokens(a), sig_tokens(b)
    if not ta or not tb:
        return False
    return len(ta & tb) / len(ta | tb) >= threshold


def claim_blockers(leases, dead, node, family, sig, reason=None, at=None):
    """The diversity rule. `reason` is a --same-family or --revive reason;
    `at` ignores leases that had expired by that time."""
    out = []
    for lease in leases.values():
        if lease.get("node") != node:
            continue
        if at is not None and at > lease["last_beat"] + lease["ttl"]:
            continue
        if same_idea(lease.get("sig"), sig):
            out.append(f"same idea active: {lease['agent']} '{lease['sig']}'")
        elif lease.get("family") == family and not reason:
            out.append(f"family {family} active: {lease['agent']} "
                       f"'{lease['sig']}' (pass --same-family REASON to share)")
    for d in dead:
        if d.get("node") == node and same_idea(d.get("sig"), sig) and not reason:
            out.append(f"recorded dead by {d['agent']}: '{d.get('sig')}' — "
                       f"{d.get('text') or 'no reason given'} (pass --revive REASON)")
    return out


def fold(events, now=None):
    """Replay the log. Events are replayed in (ts, id) order and every claim is
    re-checked against the diversity rule at that point, so logs merged from
    several containers fold to the same leases everywhere: of two claims on
    the same idea made concurrently in different places, the earlier wins and
    the later is listed under `rejected`."""
    now = time.time() if now is None else now
    leases, dead, done, needs, lemmas, sparks, families = {}, [], [], {}, [], {}, {}
    rejected = {}
    closed_refs = set()
    for e in sorted(events, key=lambda e: (e.get("ts", 0), e["id"])):
        k, node, ag = e["kind"], e.get("node"), e.get("agent")
        if k == "claim":
            blockers = claim_blockers(leases, dead, node, e.get("family"), e.get("sig"),
                                      e.get("note"), at=e["ts"])
            if blockers:
                rejected[e["id"]] = dict(e, blockers=blockers)
                continue
            leases[e["id"]] = dict(e, last_beat=e["ts"],
                                   ttl=e.get("ttl", DEFAULT_TTL))
            if e.get("ref"):
                closed_refs.add(e["ref"])  # adopting a spark
        elif k == "heartbeat":
            for lease in leases.values():
                if lease["agent"] == ag and (not node or lease.get("node") == node):
                    lease["last_beat"] = e["ts"]
                    if e.get("text"):
                        lease["progress"] = e["text"]
        elif k in ("release", "dead"):
            for lid in [lid for lid, lease in leases.items()
                        if lease["agent"] == ag and lease.get("node") == node
                        and (not e.get("sig") or same_idea(lease.get("sig"), e["sig"]))]:
                lease = leases.pop(lid)
                (dead if k == "dead" else done).append(dict(
                    lease, outcome=e.get("outcome") or k, text=e.get("text"),
                    closed_ts=e["ts"]))
            if k == "dead" and not any(d.get("closed_ts") == e["ts"] and d["agent"] == ag
                                       for d in dead):
                dead.append(dict(e, closed_ts=e["ts"]))  # a dead end with no lease
        elif k == "need":
            needs[e["id"]] = e
        elif k == "spark":
            sparks[e["id"]] = e
        elif k == "lemma":
            lemmas.append(e)
        elif k == "family":
            families[e.get("family")] = e
        if e.get("ref") and k in ("lemma", "answer", "release", "dead"):
            closed_refs.add(e["ref"])
    expired = [lease for lease in leases.values()
               if now > lease["last_beat"] + lease["ttl"]]
    for lease in expired:
        leases.pop(lease["id"], None)
    return {"leases": leases, "expired": expired, "rejected": rejected,
            "dead": dead, "done": done,
            "needs": {i: n for i, n in needs.items() if i not in closed_refs},
            "lemmas": lemmas,
            "sparks": {i: s for i, s in sparks.items() if i not in closed_refs},
            "families": families}


def in_wave(events, wave, all_waves):
    return events if all_waves else [e for e in events if e.get("wave") == wave]


# ---------------------------------------------------------------------------
# Graph helpers
# ---------------------------------------------------------------------------

_GRAPH = None


def graph():
    global _GRAPH
    if _GRAPH is None:
        _GRAPH, _ = cairn.compile_graph()
    return _GRAPH


def load_paradigms(extra=None):
    with open(PARADIGMS, encoding="utf-8") as f:
        p = json.load(f)
    for name, e in (extra or {}).items():
        if name and name not in p["families"]:
            p["families"][name] = {"gist": e.get("text", ""),
                                   "keywords": e.get("keywords") or [name]}
    for spec in p["families"].values():
        spec["re"] = re.compile("|".join(spec["keywords"]), re.I)
    return p


CALIBRATION_RE = re.compile(r"off groups|non-unimodular|calibration off|every proof must fail",
                            re.I)


def attempts_section(body):
    m = re.search(r"^## Attempts\s*$(.*?)(?=^## |\Z)", body or "", re.M | re.S)
    return m.group(1) if m else ""


def attempt_items(body):
    """Top-level bullets of `## Attempts`; nested bullets stay inside their item."""
    return [item.strip() for item in re.split(r"\n-\s+", "\n" + attempts_section(body))
            if item.strip()]


def families_of(text, paradigms):
    return [name for name, spec in paradigms["families"].items()
            if spec["re"].search(text or "")]


def bounty(cid):
    """1 + the number of claims that would establish if `cid` did."""
    g = graph()
    if cid not in g.claims or g.claims[cid].status != "OPEN":
        return 0
    est, _, _, _, stable = g._solve(forced=frozenset([cid]))
    return 1 + len(est - g.established - {cid}) if stable else 1


def neighbourhood(gid):
    """The goal's live cone, plus claims named in their distinct_from and the
    routes into cone claims (where dead and partial attempts sit)."""
    g = graph()
    cone = cairn.goal_cone(g, gid)
    near = set(cone)
    for cid in cone:
        df = g.claims[cid].meta.get("distinct_from")
        if isinstance(df, dict):
            near.update(k for k in df if k in g.claims)
    routes = {rid for cid in cone for rid in g.routes_into.get(cid, [])}
    return cone, near, routes


def atlas(gid, paradigms, events=()):
    g = graph()
    if gid not in g.claims:
        raise SystemExit(f"unknown claim {gid!r}")
    cone, near, routes = neighbourhood(gid)
    fams = paradigms["families"]
    local = {f: {"established": 0, "open": 0, "refuted": 0, "attempts": 0,
                 "live": 0, "dead_live": 0, "examples": []} for f in fams}
    for nid in sorted(near | routes):
        n = g.nodes[nid]
        head = f"{n.title}\n{n.body[:2000]}"
        for f in families_of(head, paradigms):
            row = local[f]
            st = n.status or ""
            if st in ("ESTABLISHED", "COMPLETE"):
                row["established"] += 1
            elif st in ("REFUTED", "INVALIDATED"):
                row["refuted"] += 1
            else:
                row["open"] += 1
            if len(row["examples"]) < 3:
                row["examples"].append(nid)
        for f in families_of(attempts_section(n.body), paradigms):
            local[f]["attempts"] += 1
    state = fold(list(events))
    for lease in state["leases"].values():
        if lease.get("node") in near and lease.get("family") in local:
            local[lease["family"]]["live"] += 1
    for d in state["dead"]:
        if d.get("node") in near and d.get("family") in local:
            local[d["family"]]["dead_live"] += 1
    glob = {f: 0 for f in fams}
    gtoks = sig_tokens(g.claims[gid].title)
    sources = {f: [] for f in fams}
    for cid, c in g.claims.items():
        if c.status != "ESTABLISHED" or cid in near:
            continue
        for f in families_of(c.title, paradigms):
            glob[f] += 1
            overlap = len(gtoks & sig_tokens(c.title))
            sources[f].append((overlap, cid))
    rows = []
    for f in fams:
        L = local[f]
        size = L["established"] + L["open"] + L["refuted"]
        rows.append({"family": f, "gist": fams[f].get("gist", ""), "near": size,
                     **{k: L[k] for k in ("established", "open", "refuted",
                                          "attempts", "live", "dead_live", "examples")},
                     "global_established": glob[f],
                     "transplant_sources": [cid for _, cid in
                                            sorted(sources[f], key=lambda x: (-x[0], x[1]))[:3]]})
    sizes = sorted(r["near"] for r in rows)
    hot_cut = sizes[int(len(sizes) * 0.75)] if sizes else 0
    near_total = sum(sizes) or 1
    glob_total = sum(glob.values()) or 1
    for r in rows:
        dying = r["attempts"] + r["refuted"] + r["dead_live"]
        # Coldness: how under-represented the family is here, relative to its
        # share of established work in the whole graph.
        share_here = r["near"] / near_total
        share_graph = r["global_established"] / glob_total
        r["representation"] = round(share_here / share_graph, 2) if share_graph else None
        if r["global_established"] >= 20 and share_graph and share_here < 0.35 * share_graph:
            r["temperature"] = "COLD"
        elif r["near"] >= hot_cut and r["near"] > 0:
            r["temperature"] = "HOT"
        else:
            r["temperature"] = "warm"
        r["dying"] = dying
    vocab = set()
    for cid in cone:
        vocab |= sig_tokens(g.claims[cid].title)
    scored = []
    for cid, c in g.claims.items():
        if c.status == "ESTABLISHED" and CALIBRATION_RE.search(f"{c.title}\n{c.body}"):
            score = len(vocab & sig_tokens(c.title)) + (3 if cid in near else 0)
            if score >= 2:
                scored.append((score, cid))
    calib = [cid for _, cid in sorted(scored, key=lambda x: (-x[0], x[1]))[:6]]
    return {"goal": gid, "cone": len(cone), "neighbourhood": len(near),
            "routes": len(routes), "families": rows, "calibration": calib}


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------

def out(args, payload, human):
    print(json.dumps(payload, indent=1, ensure_ascii=False) if args.json else human)


def fmt_age(seconds):
    s = int(max(0, seconds))
    return f"{s // 3600}h{(s % 3600) // 60:02d}m" if s >= 3600 else f"{s // 60}m{s % 60:02d}s"


def parse_ttl(text):
    m = re.fullmatch(r"(\d+)([smhd]?)", str(text))
    if not m:
        raise SystemExit(f"bad ttl {text!r}; use e.g. 90m, 4h")
    return int(m[1]) * {"": 1, "s": 1, "m": 60, "h": 3600, "d": 86400}[m[2]]


def check_node(nid, allow_new):
    if not cairn.ID_RE.fullmatch(nid or ""):
        raise SystemExit(f"malformed id {nid!r}: want ^[a-z0-9][a-z0-9-]{{1,63}}$")
    if not allow_new and nid not in graph().nodes:
        near = cairn.similar_nodes(nid.replace("-", " "), graph().claims, limit=3,
                                   threshold=0.3, min_overlap=1)
        hint = ", ".join(n.id for _, n in near)
        raise SystemExit(f"{nid!r} is not in the graph (pass --new for a node you are "
                         f"creating){'; nearest: ' + hint if hint else ''}")


def cmd_claim(args):
    require_agent()
    check_node(args.node, args.new)
    paradigms = load_paradigms(fold(read_events())["families"])
    if args.family not in paradigms["families"]:
        raise SystemExit(f"unknown family {args.family!r}; known: "
                         + ", ".join(paradigms["families"])
                         + ". Invent one with `cairn-live family add`.")
    auto_pull(force=True)
    with _Locked("claim.lock"):
        state = fold(read_events())
        blockers = claim_blockers(state["leases"], state["dead"], args.node, args.family,
                                  args.sig, args.same_family or args.revive)
        if blockers:
            print("BLOCKED\n  " + "\n  ".join(blockers), file=sys.stderr)
            return EXIT_BLOCKED
        e = append("claim", node=args.node, family=args.family, sig=args.sig,
                   text=args.intent, ttl=parse_ttl(args.ttl), ref=args.adopt,
                   note=args.same_family or args.revive)
    if not confirm_claim(e):
        return EXIT_BLOCKED
    print(f"claimed {args.node} [{args.family}] '{args.sig}' as {e['agent']} "
          f"(ttl {fmt_age(e['ttl'])}; heartbeat to keep it)")
    return EXIT_OK


def cmd_post(args):
    args.node = args.node or getattr(args, "node_opt", None)
    if args.kind in ("release", "dead"):
        require_agent()
    if args.node:
        check_node(args.node, True)
    files = [f for f in (args.files or [])]
    missing = [f for f in files if not os.path.exists(os.path.join(ROOT, f))
               and not os.path.exists(f)]
    if missing:
        raise SystemExit("files not found: " + ", ".join(missing))
    fields = dict(node=args.node, family=args.family, sig=args.sig, text=args.text,
                  files=files, ref=args.ref, outcome=args.outcome)
    if args.kind == "need" and args.node and args.node in graph().claims:
        fields["bounty"] = bounty(args.node)
    if args.kind == "family":
        fields["keywords"] = [k.strip() for k in (args.keywords or "").split(",") if k.strip()]
    e = append(args.kind, **fields)
    print(f"posted {e['kind']} {e['id'][:8]}" + (f" on {e['node']}" if e.get("node") else ""))
    if args.kind == "lemma":
        text = " ".join(filter(None, [args.text, args.keywords,
                                      args.node and args.node.replace("-", " ")]))
        g = graph()
        opens = {i: c for i, c in g.claims.items() if c.status == "OPEN" and i != args.node}
        hits = cairn.similar_nodes(text, opens, limit=5, threshold=0.35, min_overlap=2)
        if hits:
            append("transfer", node=args.node, ref=e["id"],
                   text="may feed: " + ", ".join(n.id for _, n in hits),
                   targets=[n.id for _, n in hits])
            print("transfer candidates (open claims this may feed):")
            for score, n in hits:
                print(f"  {score:.2f} {n.id}  {n.title}")
    return EXIT_OK


def cmd_heartbeat(args):
    require_agent()
    append("heartbeat", node=args.node, text=args.text)
    return EXIT_OK


def cursor_path(agent):
    safe = re.sub(r"[^A-Za-z0-9._-]+", "_", agent)
    d = os.path.join(live_dir(), "cursors")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, safe)


def fmt_event(e, now):
    bits = [f"{fmt_age(now - e['ts'])} ago", e["agent"], e["kind"].upper()]
    if e.get("node"):
        bits.append(e["node"])
    if e.get("family"):
        bits.append(f"[{e['family']}]")
    if e.get("sig"):
        bits.append(f"'{e['sig']}'")
    if e.get("bounty"):
        bits.append(f"bounty={e['bounty']}")
    line = "  ".join(bits)
    if e.get("text"):
        line += f"\n      {e['text']}"
    if e.get("files"):
        line += "\n      files: " + ", ".join(e["files"])
    return line


def cmd_feed(args):
    kinds = set(args.kind.split(",")) if args.kind else None
    cone = None
    if args.cone:
        cone = neighbourhood(args.cone)[1]

    def select(events):
        return [e for e in in_wave(events, wave_name(), args.all_waves)
                if (not kinds or e["kind"] in kinds)
                and (not args.node or e.get("node") == args.node)
                and (cone is None or not e.get("node") or e["node"] in cone)
                and (args.mine or e["agent"] != agent_name() or not args.new)]

    events = read_events()
    start = 0
    if args.new:
        try:
            with open(cursor_path(agent_name())) as f:
                start = int(f.read().strip() or 0)
        except (OSError, ValueError):
            start = 0
    chosen = select(events[start:])
    if args.tail:
        chosen = chosen[-args.tail:]
    now = time.time()
    if args.json:
        print(json.dumps(chosen, indent=1, ensure_ascii=False))
    else:
        print("\n".join(fmt_event(e, now) for e in chosen) or "(nothing new)")
    if args.new:
        with open(cursor_path(agent_name()), "w") as f:
            f.write(str(len(events)))
    while args.follow:
        time.sleep(args.interval)
        fresh = read_events()
        new = select(fresh[len(events):])
        events = fresh
        if new:
            now = time.time()
            print("\n".join(fmt_event(e, now) for e in new), flush=True)
        if args.new:
            with open(cursor_path(agent_name()), "w") as f:
                f.write(str(len(events)))
    return EXIT_OK


def cmd_board(args):
    events = in_wave(read_events(), wave_name(), args.all_waves)
    s = fold(events)
    now = time.time()
    L = [f"wave {'(all)' if args.all_waves else wave_name()}: {len(events)} events, "
         f"{len(s['leases'])} active leases, {len(s['needs'])} open needs, "
         f"{len(s['lemmas'])} lemmas, {len(s['dead'])} dead approaches"]
    by_node = {}
    for lease in s["leases"].values():
        by_node.setdefault(lease.get("node"), []).append(lease)
    L.append("\nACTIVE")
    for node in sorted(by_node):
        L.append(f"  {node}")
        for lease in sorted(by_node[node], key=lambda x: x["ts"]):
            stale = now - lease["last_beat"] > lease["ttl"] / 2
            L.append(f"    {lease['agent']:<18} [{lease.get('family')}] '{lease.get('sig')}'"
                     f"  beat {fmt_age(now - lease['last_beat'])} ago"
                     + ("  STALE" if stale else "")
                     + (f"\n      {lease['progress']}" if lease.get("progress") else ""))
    if not by_node:
        L.append("  (none)")
    L.append("\nNEEDS (by bounty)")
    for n in sorted(s["needs"].values(), key=lambda n: (-n.get("bounty", 0), n["ts"])):
        L.append(f"  {n['id'][:8]} bounty={n.get('bounty', '?')} {n.get('node', '')}  "
                 f"from {n['agent']}: {n.get('text', '')}")
    if not s["needs"]:
        L.append("  (none)")
    L.append("\nRECENT LEMMAS")
    for e in s["lemmas"][-args.recent:]:
        L.append(f"  {e.get('node', '')}  by {e['agent']}: {e.get('text', '')}")
    if not s["lemmas"]:
        L.append("  (none)")
    L.append("\nDEAD APPROACHES")
    for d in s["dead"][-args.recent:]:
        L.append(f"  {d.get('node', '')} [{d.get('family')}] '{d.get('sig')}': "
                 f"{d.get('text') or ''}")
    if not s["dead"]:
        L.append("  (none)")
    if s["sparks"]:
        L.append("\nUNADOPTED SPARKS (claim with --adopt ID)")
        for sp in list(s["sparks"].values())[-args.recent:]:
            where = " ".join(filter(None, [sp.get("node"), sp.get("family") and f"[{sp['family']}]"]))
            L.append(f"  {sp['id'][:8]} {where + ' ' if where else ''}"
                     f"from {sp['agent']}: {sp.get('text', '')}")
    payload = {"leases": list(s["leases"].values()), "needs": list(s["needs"].values()),
               "lemmas": s["lemmas"], "dead": s["dead"], "sparks": list(s["sparks"].values())}
    out(args, payload, "\n".join(L))
    return EXIT_OK


def cmd_approaches(args):
    g = graph()
    if args.node not in g.nodes:
        raise SystemExit(f"unknown node {args.node!r}")
    paradigms = load_paradigms(fold(read_events())["families"])
    n = g.nodes[args.node]
    s = fold(read_events())
    L = [f"{args.node} [{n.status}] {n.title}", "", "IN THE GRAPH"]
    for rid in g.routes_into.get(args.node, []):
        r = g.routes[rid]
        fam = ",".join(families_of(f"{r.title}\n{r.body[:2000]}", paradigms)) or "-"
        L.append(f"  route {rid} [{r.status}] ({fam})")
    for item in attempt_items(n.body):
        head = re.match(r"\*\*(.+?)\*\*", item)
        fam = ",".join(families_of(item, paradigms)) or "-"
        L.append(f"  attempt: {head[1] if head else item.splitlines()[0][:80]} ({fam})")
    L.append("\nLIVE (all waves)")
    for lease in s["leases"].values():
        if lease.get("node") == args.node:
            L.append(f"  active {lease['agent']} [{lease.get('family')}] '{lease.get('sig')}'")
    for d in s["dead"]:
        if d.get("node") == args.node:
            L.append(f"  dead   {d['agent']} [{d.get('family')}] '{d.get('sig')}': {d.get('text') or ''}")
    for d in s["done"]:
        if d.get("node") == args.node:
            L.append(f"  done   {d['agent']} [{d.get('family')}] '{d.get('sig')}': {d.get('text') or ''}")
    used = {x.get("family") for x in list(s["leases"].values()) + s["dead"]
            if x.get("node") == args.node}
    L.append("\nFAMILIES NOT YET TRIED LIVE ON THIS NODE: "
             + ", ".join(f for f in paradigms["families"] if f not in used))
    print("\n".join(L))
    return EXIT_OK


def cmd_atlas(args):
    paradigms = load_paradigms(fold(read_events())["families"])
    a = atlas(args.goal, paradigms, read_events())
    L = [f"ATLAS {a['goal']}: cone {a['cone']} claims, neighbourhood {a['neighbourhood']}, "
         f"{a['routes']} routes", "",
         "near = tagged nodes in the neighbourhood; dead = attempts, refutations, live dead ends;",
         "rep = share here / share of established work graph-wide (COLD when < 0.35)", "",
         f"{'family':<24} {'temp':<5} {'near':>4} {'est':>4} {'open':>4} {'dead':>4} "
         f"{'live':>4} {'global✓':>7} {'rep':>5}"]
    for r in sorted(a["families"], key=lambda r: (r["temperature"] != "COLD", -r["near"])):
        L.append(f"{r['family']:<24} {r['temperature']:<5} {r['near']:>4} {r['established']:>4} "
                 f"{r['open']:>4} {r['dying']:>4} {r['live']:>4} {r['global_established']:>7} "
                 f"{r['representation'] if r['representation'] is not None else '-':>5}")
    cold = [r for r in a["families"] if r["temperature"] == "COLD"]
    if cold:
        L.append("\nCOLD: established elsewhere, almost absent here (transplant candidates)")
        for r in cold:
            L.append(f"  {r['family']}: {r['gist']}\n    sources: "
                     + ", ".join(r["transplant_sources"]))
    if a["calibration"]:
        L.append("\nCALIBRATION NODES (every proof must fail on these worlds)")
        L += [f"  {c}" for c in a["calibration"]]
    L.append("\nKeyword tagging is coarse: read it as where to look, not as a census.")
    out(args, a, "\n".join(L))
    return EXIT_OK


def cmd_card(args):
    paradigms = load_paradigms(fold(read_events())["families"])
    if args.role not in paradigms["roles"]:
        raise SystemExit("unknown role; known: " + ", ".join(paradigms["roles"]))
    g = graph()
    a = atlas(args.goal, paradigms, read_events())
    rows = {r["family"]: r for r in a["families"]}
    hot = [f for f, r in rows.items() if r["temperature"] == "HOT"]
    cold = [f for f, r in rows.items() if r["temperature"] == "COLD"]
    s = fold(read_events())
    cone, near, routes = neighbourhood(args.goal)
    per_node = []
    for nid in sorted(cone):
        heads = [m[1] for m in (re.match(r"\*\*(.+?)\*\*", it) for it in attempt_items(g.nodes[nid].body)) if m]
        if heads:
            per_node.append([f"{nid}: {h}" for h in heads])
    dead_graph = []  # round-robin, so one heavily attempted node cannot fill the card
    while any(per_node):
        for q in per_node:
            if q:
                dead_graph.append(q.pop(0))
    census = [nid for nid in sorted(near) if "census" in nid]
    L = [f"ROLE: {args.role}   GOAL: {args.goal} — {g.claims[args.goal].title}", "",
         paradigms["roles"][args.role], ""]
    if args.node:
        if args.node not in g.nodes:
            raise SystemExit(f"unknown node {args.node!r}")
        t = g.nodes[args.node]
        L.append(f"TARGET {args.node} [{t.status}] {t.title}")
        if t.status == "OPEN" and args.node in g.claims:
            L.append(f"  bounty {bounty(args.node)} (1 + claims that establish with it)")
        heads = [m[1] for m in (re.match(r"\*\*(.+?)\*\*", it) for it in attempt_items(t.body)) if m]
        if heads:
            L.append("  its recorded attempts: " + " | ".join(heads))
        mine = [l for l in s["leases"].values() if l.get("node") == args.node]
        if mine:
            L.append("  live on it now: " + " | ".join(
                f"{l['agent']} [{l.get('family')}] '{l.get('sig')}'" for l in mine))
        L.append("")
    L += [
         "HOT families here (do not spend the run inside these unless you break their shared assumption): "
         + (", ".join(hot) or "(none)"),
         "COLD families (established elsewhere, absent here):"]
    L += [f"  {f}: {rows[f]['gist']} — e.g. {', '.join(rows[f]['transplant_sources'])}"
          for f in cold] or ["  (none)"]
    L.append("DEAD approaches recorded in the cone (read these; do not retry them):")
    L += [f"  {d}" for d in dead_graph[:args.limit]] or ["  (none recorded)"]
    live_dead = [d for d in s["dead"] if d.get("node") in near]
    if live_dead:
        L.append("DEAD approaches from live waves:")
        L += [f"  {d.get('node')} [{d.get('family')}] '{d.get('sig')}': {d.get('text') or ''}"
              for d in live_dead[-args.limit:]]
    if a["calibration"]:
        L.append("CALIBRATION nodes: " + ", ".join(a["calibration"]))
    if census:
        L.append("CENSUS nodes already run: " + ", ".join(census))
    L += ["", "PROTOCOL",
          "  1. Before building anything, check novelty: `bin/cairn search \"<your idea in one line>\"`"
          " and `bin/cairn-live approaches <node>`. Name the nearest node and say what is structurally new.",
          "  2. `bin/cairn-live claim <node> --family <family> --sig \"<idea in 3-8 words>\" --intent \"<first falsifiable step>\"`."
          " Exit 3 means the idea is taken or dead: change the idea, not the wording.",
          "  3. Between steps: `bin/cairn-live feed --new --cone " + args.goal + "` and `bin/cairn-live heartbeat --node <node> --text \"<progress>\"`.",
          "  4. Post what others can use the moment you have it: `lemma` (with files), `need` (a sub-claim you are blocked on),"
          " `spark` (an idea you will not pursue), and `dead` with where it dies.",
          "  5. Finish with `release` or `dead`. Either way, write the Cairn nodes (new claims, routes, ## Attempts) so the idea outlives the wave."]
    print("\n".join(L))
    return EXIT_OK


# ---------------------------------------------------------------------------
# Dispatch: a pull-based work queue computed from the graph and the log
# ---------------------------------------------------------------------------

# Which families a role takes on a node. `rows` is the atlas; `dead_by_family`
# counts recorded attempts and live dead ends on the node.
ROLE_WEIGHT = {"obstruction-miner": 1.2, "transplanter": 1.2, "inverter": 1.0,
               "reframer": 1.0, "scale-shifter": 1.0, "heretic": 0.9,
               "calibrator": 0.8, "compute-scout": 0.8}
TEMP_NOVELTY = {"COLD": 3.0, "warm": 1.5, "HOT": 0.6}


def role_families(role, rows, dead_by_family):
    temps = {f: r["temperature"] for f, r in rows.items()}
    if role == "transplanter":
        return [f for f, t in temps.items() if t == "COLD"]
    if role == "heretic":
        return [f for f, t in temps.items() if t == "HOT"]
    if role == "obstruction-miner":
        return [f for f, n in sorted(dead_by_family.items(), key=lambda x: -x[1]) if n >= 2][:2]
    if role == "calibrator":
        return ["calibration"] if "calibration" in rows else []
    if role == "compute-scout":
        return ["census-computation"] if "census-computation" in rows else []
    fixed = {"inverter": "minimal-counterexample", "reframer": "reframing",
             "scale-shifter": "quantifier-shift"}
    return [fixed[role]] if fixed.get(role) in rows else []


def cone_bounties(gid, holes):
    """Bounty per hole, cached in the live dir against the established set."""
    g = graph()
    key = hashlib.sha1(("\n".join(sorted(g.established)) + "|" + gid).encode()).hexdigest()
    path = os.path.join(live_dir(), "bounty-cache.json")
    try:
        with open(path) as f:
            cache = json.load(f)
    except (OSError, ValueError):
        cache = {}
    if cache.get("key") != key:
        cache = {"key": key, "bounties": {}}
    todo = [h for h in holes if h not in cache["bounties"]]
    for h in todo:
        cache["bounties"][h] = bounty(h)
    if todo:
        tmp = path + f".{os.getpid()}"
        with open(tmp, "w") as f:
            json.dump(cache, f)
        os.replace(tmp, path)
    return {h: cache["bounties"][h] for h in holes}


def dispatch_slots(gid, slots, explore, events):
    import math
    g = graph()
    paradigms = load_paradigms(fold(events)["families"])
    a = atlas(gid, paradigms, events)
    rows = {r["family"]: r for r in a["families"]}
    state = fold(events)
    cone = cairn.goal_cone(g, gid)
    holes = sorted(c for c in cone if g.claims[c].status == "OPEN")
    bounties = cone_bounties(gid, holes)
    need_boost, transfer_targets = {}, {}
    for n in state["needs"].values():
        if n.get("node") in bounties:
            need_boost[n["node"]] = need_boost.get(n["node"], 0) + 1
    for e in events:
        if e["kind"] == "transfer":
            for t in e.get("targets", []):
                transfer_targets.setdefault(t, e.get("ref"))
    cands = []
    for node in holes + [t for t in transfer_targets if t in g.claims and t not in holes
                         and g.claims[t].status == "OPEN"]:
        body = g.nodes[node].body
        dead_by_family = {}
        for item in attempt_items(body):
            for f in families_of(item, paradigms):
                dead_by_family[f] = dead_by_family.get(f, 0) + 1
        for d in state["dead"]:
            if d.get("node") == node and d.get("family"):
                dead_by_family[d["family"]] = dead_by_family.get(d["family"], 0) + 1
        live_families = {l.get("family") for l in state["leases"].values() if l.get("node") == node}
        base = math.log2(1 + max(1, bounties.get(node, 1))) * (1 + 0.5 * need_boost.get(node, 0))
        for role, weight in ROLE_WEIGHT.items():
            for f in role_families(role, rows, dead_by_family):
                if f in live_families:
                    continue
                reasons = [f"bounty {bounties.get(node, '?')}"]
                score = base * weight
                if role == "obstruction-miner":
                    score *= 1 + dead_by_family.get(f, 0) / 3
                    reasons.append(f"{dead_by_family.get(f, 0)} dead {f} attempts to mine")
                else:
                    score *= TEMP_NOVELTY.get(rows[f]["temperature"], 1.0)
                    score /= 1 + dead_by_family.get(f, 0) / 2
                    reasons.append(f"{f} is {rows[f]['temperature']} here")
                if need_boost.get(node):
                    reasons.append(f"{need_boost[node]} open live need(s)")
                if node in transfer_targets:
                    score *= 2 if role == "transplanter" else 1.2
                    reasons.append(f"a live lemma may feed it ({transfer_targets[node][:8]})")
                cands.append({"node": node, "role": role, "family": f, "score": score,
                              "explore": rows[f]["temperature"] == "COLD" or rows[f]["near"] <= 3,
                              "reasons": reasons})
    picked, count = [], {}
    n_explore = math.ceil(explore * slots)

    def adjusted(c):
        s = c["score"]
        s *= 0.5 ** count.get(("node", c["node"]), 0)
        s *= 0.7 ** count.get(("role", c["role"]), 0)
        s *= 0.6 ** count.get(("family", c["family"]), 0)
        return s

    while len(picked) < slots and cands:
        need_explore = sum(p["explore"] for p in picked) < n_explore \
            and slots - len(picked) <= n_explore - sum(p["explore"] for p in picked)
        pool = [c for c in cands if c["explore"]] if need_explore else cands
        pool = pool or cands
        best = max(pool, key=adjusted)
        best = dict(best, score=round(adjusted(best), 2))
        picked.append(best)
        cands = [c for c in cands if not (c["node"] == best["node"] and c["family"] == best["family"])]
        for k in (("node", best["node"]), ("role", best["role"]), ("family", best["family"])):
            count[k] = count.get(k, 0) + 1
    for p in picked:
        p["card"] = f"bin/cairn-live card {p['role']} {gid} --node {p['node']}"
        p["sig"] = f"{p['role']} via {p['family']}"
    return picked


def cmd_dispatch(args):
    auto_pull(force=args.take)
    events = read_events()
    if args.take:
        require_agent()
        with _Locked("claim.lock"):
            events = read_events()
            slots = dispatch_slots(args.goal, max(args.slots, 1), args.explore, events)
            if args.role:
                slots = [x for x in slots if x["role"] == args.role]
            if not slots:
                print("nothing to take", file=sys.stderr)
                return EXIT_BLOCKED
            x = slots[0]
            e = append("claim", node=x["node"], family=x["family"], sig=x["sig"],
                       text="dispatched: " + "; ".join(x["reasons"]), ttl=DEFAULT_TTL,
                       role=x["role"])
        if not confirm_claim(e):
            return EXIT_BLOCKED
        x["lease"] = e["id"]
        if args.json:
            print(json.dumps(x, indent=1))
        else:
            print(f"took {x['role']} on {x['node']} [{x['family']}] ({'; '.join(x['reasons'])})\n"
                  f"brief: {x['card']}")
        return EXIT_OK
    slots = dispatch_slots(args.goal, args.slots, args.explore, events)
    if args.json:
        print(json.dumps(slots, indent=1))
    else:
        for i, x in enumerate(slots, 1):
            print(f"{i:>2}. {x['score']:>5}  {x['role']:<18} {x['node']}  [{x['family']}]"
                  + ("  EXPLORE" if x["explore"] else "")
                  + f"\n      {'; '.join(x['reasons'])}\n      {x['card']}")
    return EXIT_OK


def cmd_family(args):
    if args.action == "list":
        paradigms = load_paradigms(fold(read_events())["families"])
        for name, spec in paradigms["families"].items():
            print(f"{name:<24} {spec.get('gist', '')}")
        return EXIT_OK
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]{1,40}", args.name or ""):
        raise SystemExit("family name must be kebab-case")
    append("family", family=args.name, text=args.text,
           keywords=[k.strip() for k in (args.keywords or args.name).split(",") if k.strip()])
    print(f"family {args.name} added to the live taxonomy")
    return EXIT_OK


def cmd_export(args):
    events = in_wave(read_events(), wave_name(), args.all_waves)
    with open(args.path, "w", encoding="utf-8") as f:
        for e in events:
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    print(f"exported {len(events)} events to {args.path}")
    return EXIT_OK


def cmd_import(args):
    n = merge_events(read_events(args.path))
    print(f"imported {n} new events")
    return EXIT_OK


def _git(*a, input_=None):
    return subprocess.run(["git", "-C", ROOT, *a], input=input_, capture_output=True,
                          text=True)


def sync_target():
    """CAIRN_LIVE_SYNC=REMOTE turns on replication for every command; the ref
    is CAIRN_LIVE_REF, default refs/cairn-live/<wave>."""
    remote = os.environ.get("CAIRN_LIVE_SYNC")
    if not remote:
        return None
    return remote, os.environ.get("CAIRN_LIVE_REF") or f"refs/cairn-live/{wave_name()}"


def auto_pull(force=False):
    target = sync_target()
    if not target:
        return
    stamp = os.path.join(live_dir(), "last-pull")
    every = float(os.environ.get("CAIRN_LIVE_PULL_EVERY", "15"))
    try:
        if not force and time.time() - os.path.getmtime(stamp) < every:
            return
    except OSError:
        pass
    sync_once(*target, pull_only=True, quiet=True)
    with open(stamp, "w"):
        pass


def auto_push():
    target = sync_target()
    if target and sync_once(*target, quiet=True) != 0:
        print("warning: cairn-live sync failed; events are local until the next sync",
              file=sys.stderr)


def confirm_claim(e):
    """After replication, keep the claim only if the merged log still admits it."""
    if not sync_target():
        return True
    auto_push()
    state = fold(read_events())
    if e["id"] in state["leases"]:
        return True
    print("BLOCKED (lost a concurrent claim in another container)\n  "
          + "\n  ".join(state["rejected"].get(e["id"], {}).get("blockers", [])),
          file=sys.stderr)
    return False


def cmd_sync(args):
    return sync_once(args.remote, args.ref or f"refs/cairn-live/{wave_name()}",
                     args.pull_only, args.retries)


def sync_once(remote, ref, pull_only=False, retries=8, quiet=False):
    """Replicate the log through a git ref, for agents in other containers.
    The ref holds one file, events.jsonl. Merge is a union by event id, so
    concurrent syncs never conflict; a rejected push just syncs again."""
    say = (lambda *a: None) if quiet else print
    ref = ref if ref.startswith("refs/") else f"refs/heads/{ref}"
    pushed = None
    for attempt in range(retries):
        fetched = _git("fetch", "-q", remote, f"+{ref}:refs/cairn-live/remote")
        parent = None
        if fetched.returncode == 0:
            parent = _git("rev-parse", "refs/cairn-live/remote").stdout.strip()
            blob = _git("show", "refs/cairn-live/remote:events.jsonl")
            if blob.returncode == 0:
                incoming = []
                for line in blob.stdout.splitlines():
                    try:
                        incoming.append(json.loads(line))
                    except json.JSONDecodeError:
                        pass
                say(f"pulled {merge_events(incoming)} new events")
        if pull_only:
            return EXIT_OK
        with open(log_path(), encoding="utf-8") as f:
            data = f.read()
        sha = _git("hash-object", "-w", "--stdin", input_=data).stdout.strip()
        tree = _git("mktree", input_=f"100644 blob {sha}\tevents.jsonl\n").stdout.strip()
        if parent and _git("rev-parse", f"{parent}^{{tree}}").stdout.strip() == tree:
            say("remote already up to date")
            return EXIT_OK
        cmd = ["commit-tree", tree, "-m", f"cairn-live sync by {agent_name()}"]
        if parent:
            cmd[2:2] = ["-p", parent]
        commit = _git(*cmd).stdout.strip()
        pushed = _git("push", "-q", remote, f"{commit}:{ref}")
        if pushed.returncode == 0:
            say(f"pushed {len(read_events())} events to {remote} {ref}")
            return EXIT_OK
        time.sleep(1 + attempt)
    print(f"sync failed: {pushed.stderr.strip() if pushed else 'no attempt'}", file=sys.stderr)
    return 1


class _Parser(argparse.ArgumentParser):
    def error(self, message):
        self.print_usage(sys.stderr)
        self.exit(EXIT_USAGE, f"{self.prog}: error: {message}\n")


def main(argv=None):
    p = _Parser(prog="cairn-live", description=__doc__.split("\n")[0],
                                epilog="exit codes: 0 ok · 3 blocked (idea taken, dead, or "
                                       "family active) · 64 usage · 1 runtime")
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("claim", help="take an approach lease on a node")
    c.add_argument("node")
    c.add_argument("--family", required=True)
    c.add_argument("--sig", required=True, help="the idea in 3-8 words")
    c.add_argument("--intent", help="first falsifiable step")
    c.add_argument("--ttl", default="4h")
    c.add_argument("--new", action="store_true", help="node is being created")
    c.add_argument("--same-family", metavar="REASON")
    c.add_argument("--revive", metavar="REASON")
    c.add_argument("--adopt", metavar="SPARK_ID")
    c.set_defaults(fn=cmd_claim)

    po = sub.add_parser("post", help="append an event")
    po.add_argument("kind", choices=[k for k in KINDS if k not in ("claim", "heartbeat")])
    po.add_argument("--node")
    po.add_argument("--family")
    po.add_argument("--sig")
    po.add_argument("--text")
    po.add_argument("--files", nargs="*")
    po.add_argument("--ref", help="id of the event this answers or closes")
    po.add_argument("--outcome")
    po.add_argument("--keywords")
    po.set_defaults(fn=cmd_post)

    for kind in SHORTHAND:
        sp = sub.add_parser(kind, help=f"shorthand for post {kind}")
        sp.add_argument("node", nargs="?")
        sp.add_argument("--node", dest="node_opt", metavar="NODE")
        sp.add_argument("--family")
        sp.add_argument("--sig")
        sp.add_argument("--text")
        sp.add_argument("--files", nargs="*")
        sp.add_argument("--ref")
        sp.add_argument("--outcome")
        sp.add_argument("--keywords")
        sp.set_defaults(fn=cmd_post, kind=kind)

    h = sub.add_parser("heartbeat", help="keep leases alive, with progress")
    h.add_argument("--node")
    h.add_argument("--text")
    h.set_defaults(fn=cmd_heartbeat)

    f = sub.add_parser("feed", help="read events")
    f.add_argument("--new", action="store_true", help="since this agent's cursor, skipping its own")
    f.add_argument("--mine", action="store_true", help="with --new, include own events")
    f.add_argument("--node")
    f.add_argument("--kind", help="comma-separated kinds")
    f.add_argument("--cone", metavar="GOAL", help="only events on this goal's neighbourhood")
    f.add_argument("--tail", type=int)
    f.add_argument("--follow", action="store_true")
    f.add_argument("--interval", type=float, default=2.0)
    f.add_argument("--all-waves", action="store_true")
    f.add_argument("--json", action="store_true")
    f.set_defaults(fn=cmd_feed)

    b = sub.add_parser("board", help="who is doing what, needs, lemmas, dead ends")
    b.add_argument("--recent", type=int, default=10)
    b.add_argument("--all-waves", action="store_true")
    b.add_argument("--json", action="store_true")
    b.set_defaults(fn=cmd_board)

    ap = sub.add_parser("approaches", help="every approach to one node, graph and live")
    ap.add_argument("node")
    ap.set_defaults(fn=cmd_approaches)

    at = sub.add_parser("atlas", help="approach families around a goal: hot, dying, cold")
    at.add_argument("goal")
    at.add_argument("--json", action="store_true")
    at.set_defaults(fn=cmd_atlas)

    cd = sub.add_parser("card", help="a worker brief for a paradigm role on a goal")
    cd.add_argument("role")
    cd.add_argument("goal")
    cd.add_argument("--node", help="focus the brief on one hole")
    cd.add_argument("--limit", type=int, default=25)
    cd.set_defaults(fn=cmd_card)

    dp = sub.add_parser("dispatch", help="the next assignments: role x hole x family, scored")
    dp.add_argument("goal")
    dp.add_argument("--slots", type=int, default=8)
    dp.add_argument("--explore", type=float, default=0.3,
                    help="fraction of slots reserved for COLD or barely-touched families")
    dp.add_argument("--take", action="store_true", help="atomically claim the top slot for this agent")
    dp.add_argument("--role", help="with --take, only this role")
    dp.add_argument("--json", action="store_true")
    dp.set_defaults(fn=cmd_dispatch)

    fa = sub.add_parser("family", help="list families or add one at run time")
    fa.add_argument("action", choices=["list", "add"])
    fa.add_argument("name", nargs="?")
    fa.add_argument("--text")
    fa.add_argument("--keywords", help="comma-separated regex fragments")
    fa.set_defaults(fn=cmd_family)

    ex = sub.add_parser("export", help="write this wave's events to a file")
    ex.add_argument("path")
    ex.add_argument("--all-waves", action="store_true")
    ex.set_defaults(fn=cmd_export)

    im = sub.add_parser("import", help="union events from a file")
    im.add_argument("path")
    im.set_defaults(fn=cmd_import)

    sy = sub.add_parser("sync", help="replicate the log through a git ref")
    sy.add_argument("--ref", help="default refs/cairn-live/<wave>; never a branch without permission")
    sy.add_argument("--remote", default="origin")
    sy.add_argument("--pull-only", action="store_true")
    sy.add_argument("--retries", type=int, default=8)
    sy.set_defaults(fn=cmd_sync)

    args = p.parse_args(argv)
    if args.cmd in ("feed", "board", "approaches", "card", "atlas"):
        auto_pull()
    code = args.fn(args)
    if code == EXIT_OK and args.cmd in ("post", "heartbeat", "family") + SHORTHAND:
        auto_push()
    return code


if __name__ == "__main__":
    sys.exit(main())
