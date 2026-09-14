#!/usr/bin/env python3
"""Independent re-derivation of perturbation closures for binary four-address survivor rules.

Shares no code with experiments/gottschalk-four-address-balance (analyze2.py, gp.py, dflip.py).
Group presentations are simplified by GAP's Tietze library (TzGoGo with tracked generator images);
recognition, normal forms, the invisibility constraint problem and the merge enumeration are written
here from scratch.

Setting: memory M = {1, a, b, c}, generators a, b, c = letters 1, 2, 3 (inverse = negative letter).
A rule mu is a 16-bit table: coordinate i reads x(g m_i), input index sum bits[i] << i.
A state is a relator set R; its group G_R is <a, b, c | R>.  A state is CLOSED when every group whose
memory satisfies R has an amenable memory group or collapses the memory (m_i = m_j):
  * G_R amenable (trivial, cyclic, free product of cyclics with at most one nontrivial factor or
    Z/2 * Z/2, product of cyclics and D_infinity factors, two-generator with a normalizing relator
    h^-1 g h = g^(+-1), or finite by complete coset enumeration);
  * or two memory elements are equal in G_R (decided by the normal form).
A perturbation of a non-amenable recognized state: flip the sites F = {1, g}; choose bits on the
context sites so that every output site f m_i^-1 sees the same rule value before and after.  Then tau
is not injective in every group realizing R, unless one of these merges happens:
  (i) two context sites with different bits, (ii) a context site with a flipped site,
  (iii) the two flipped sites, (iv) two output sites.
Each merge u = v is one extra relator u^-1 v, covered by the extended state R + {u^-1 v}.
A state closes at depth 0 by a perturbation whose merges all give immediately closed states, and at
depth 1 when the non-closed merges give recognized states closing at depth 0.

Usage: replay.py <flip1.json> <analyze3.json> <dflip3.json> <gap-binary> <workdir> <mode>
  mode = replay  : the 63 rules closed by dflip3.json
  mode = open    : the survivors not closed by dflip3.json (same search, larger word list)
"""
import itertools, json, os, subprocess, sys

PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]
MEMW = [(), (1,), (2,), (3,)]


# ---------------------------------------------------------------- free group words
def freduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def winv(w):
    return tuple(-x for x in reversed(w))


def wmul(*ws):
    return freduce(tuple(x for w in ws for x in w))


def cycred(w):
    w = list(freduce(w))
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return tuple(w)


def canon_rel(w):
    """Canonical representative of the normal closure generator up to cyclic rotation and inversion."""
    w = cycred(w)
    if not w:
        return ()
    cands = []
    for v in (w, winv(w)):
        for k in range(len(v)):
            cands.append(v[k:] + v[:k])
    return min(cands)


def state_key(rels):
    return tuple(sorted({canon_rel(r) for r in rels} - {()}))


def partition_relators(labels):
    q = {p: wmul(winv(MEMW[p[0]]), MEMW[p[1]]) for p in PAIRS}
    classes = {}
    for idx, lab in enumerate(labels):
        classes.setdefault(lab, []).append(PAIRS[idx])
    rels = []
    for members in classes.values():
        rep = members[0]
        for p in members[1:]:
            rels.append(wmul(winv(q[rep]), q[p]))
    return state_key(rels)


# ---------------------------------------------------------------- GAP oracle
GAP_LIB = r'''
F := FreeGroup(3);; FAM := FamilyObj(One(F));;
W := function(l) return AssocWordByLetterRep(FAM, l); end;;
OUT := OutputTextFile(OUTNAME, false);; SetPrintFormattingStatus(OUT, false);;
Simp := function(key, rl, tryfinite)
  local G, P, gens, rels, imgs, n, tab;
  G := F / List(rl, W);
  P := PresentationFpGroup(G);;
  TzOptions(P).printLevel := 0;
  TzInitGeneratorImages(P);
  TzGoGo(P);
  gens := GeneratorsOfPresentation(P);
  rels := List(RelatorsOfPresentation(P), r -> LetterRepAssocWord(r, gens));
  imgs := List(TzImagesOldGens(P), w -> LetterRepAssocWord(w, gens));
  n := -1;
  if tryfinite then
    tab := CosetTableFromGensAndRels(FreeGeneratorsOfFpGroup(G), RelatorsOfFpGroup(G), [] : max := 300000, silent := true);
    if tab <> fail then n := Length(tab[1]); fi;
  fi;
  AppendTo(OUT, "[\"", key, "\",", Length(gens), ",", rels, ",", imgs, ",", n, "]\n");
end;;
'''


class Oracle:
    def __init__(self, gap, workdir):
        self.gap = gap
        self.work = workdir
        self.cache = {}
        self.cachefile = os.path.join(workdir, "oracle-cache.jsonl")
        self.calls = 0
        if os.path.exists(self.cachefile):
            for line in open(self.cachefile):
                rec = json.loads(line)
                self.cache[(rec["key"], rec["finite"])] = rec

    @staticmethod
    def skey(key):
        return json.dumps([list(r) for r in key], separators=(",", ":"))

    def batch(self, keys, tryfinite=False):
        todo = [k for k in dict.fromkeys(keys) if (self.skey(k), tryfinite) not in self.cache]
        for start in range(0, len(todo), 400):
            chunk = todo[start:start + 400]
            self.calls += 1
            inp = os.path.join(self.work, "batch.g")
            outn = os.path.join(self.work, "batch.out")
            with open(inp, "w") as fh:
                fh.write('OUTNAME := "%s";;\n' % outn)
                fh.write(GAP_LIB)
                for k in chunk:
                    fh.write('Simp("%s", %s, %s);;\n' % (self.skey(k).replace('"', '\\"'),
                                                        json.dumps([list(r) for r in k]),
                                                        "true" if tryfinite else "false"))
                fh.write("CloseStream(OUT);; QUIT;\n")
            subprocess.run([self.gap, "-A", "-q", "-o", "4g", inp], stdin=subprocess.DEVNULL,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=3600, check=False)
            got = {}
            if os.path.exists(outn):
                for line in open(outn):
                    line = line.strip()
                    if line:
                        k, ng, rels, imgs, n = json.loads(line)
                        got[k] = {"key": k, "finite": tryfinite, "ngens": ng, "rels": rels, "imgs": imgs, "order": n}
            with open(self.cachefile, "a") as fh:
                for k in chunk:
                    sk = self.skey(k)
                    rec = got.get(sk, {"key": sk, "finite": tryfinite, "error": True})
                    self.cache[(sk, tryfinite)] = rec
                    fh.write(json.dumps(rec) + "\n")

    def get(self, key, tryfinite=False):
        self.batch([key], tryfinite)
        return self.cache[(self.skey(key), tryfinite)]


# ---------------------------------------------------------------- recognition and normal forms
def syllables(w):
    syl = []
    for x in w:
        g, e = abs(x), (1 if x > 0 else -1)
        if syl and syl[-1][0] == g:
            syl[-1][1] += e
            if syl[-1][1] == 0:
                syl.pop()
        else:
            syl.append([g, e])
    return syl


def single_power(r):
    r = cycred(r)
    if r and all(abs(x) == abs(r[0]) for x in r):
        return abs(r[0]), abs(sum(1 if x > 0 else -1 for x in r))
    return None


def is_gen_commutator(r):
    r = cycred(r)
    if len(r) != 4:
        return None
    for v in (r, winv(r)):
        for k in range(4):
            u = v[k:] + v[:k]
            g, h = u[0], u[1]
            if abs(g) != abs(h) and u[2] == -g and u[3] == -h:
                return tuple(sorted((abs(g), abs(h))))
    return None


def is_normalizer(r, ngens):
    if ngens != 2:
        return False
    r = cycred(r)
    if len(r) != 4:
        return False
    for v in (r, winv(r)):
        for k in range(4):
            u = v[k:] + v[:k]
            # h^-1 g h g^(-+1)
            h, g = -u[0], u[1]
            if abs(h) != abs(g) and u[2] == h and abs(u[3]) == abs(g):
                return True
    return False


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def recognize(rec):
    """Return dict with 'amenable' (True/None) and optionally 'nf' (callable on words in a, b, c)."""
    if rec.get("error"):
        return {"form": "gap-error"}
    ng, rels, imgs = rec["ngens"], [tuple(r) for r in rec["rels"]], [tuple(w) for w in rec["imgs"]]
    if rec.get("order", -1) > 0:
        return {"form": "finite", "order": rec["order"], "amenable": True}
    if ng == 0:
        return {"form": "trivial", "amenable": True, "collapse": True}
    orders = {g: 0 for g in range(1, ng + 1)}
    commute = set()
    other = []
    for r in rels:
        sp = single_power(r)
        if sp is not None:
            orders[sp[0]] = gcd(orders[sp[0]], sp[1])
            continue
        c = is_gen_commutator(r)
        if c is not None:
            commute.add(c)
            continue
        other.append(r)
    sub = {g: imgs[g - 1] for g in (1, 2, 3)}

    def to_h(w):
        out = []
        for x in w:
            img = sub[abs(x)]
            out.extend(img if x > 0 else winv(img))
        return tuple(out)

    if other:
        if any(is_normalizer(r, ng) for r in other):
            return {"form": "cyclic-by-cyclic", "amenable": True}
        return {"form": "unrecognized", "ngens": ng, "rels": rec["rels"]}
    live = [g for g in orders if orders[g] != 1]
    if not live:
        return {"form": "trivial", "amenable": True, "collapse": True}
    # graph product of cyclic groups over the commutation graph (free product when no commutators)
    noncomm = {g: [h for h in live if h != g and tuple(sorted((g, h))) not in commute] for g in live}
    comps, seen = [], set()
    for g in live:
        if g in seen:
            continue
        stack, cc = [g], []
        seen.add(g)
        while stack:
            u = stack.pop()
            cc.append(u)
            for v in noncomm[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        comps.append(cc)
    amen = all(len(cc) == 1 or (len(cc) == 2 and all(orders[u] == 2 for u in cc)) for cc in comps)

    def nf(w):
        return gp_nf(to_h(w), orders, commute)

    res = {"form": "graph-product" if commute else "free-product", "orders": [orders[g] for g in live],
           "amenable": True if amen else None, "nf": nf}
    mem = [nf(m) for m in MEMW]
    res["collapse"] = len(set(mem)) < 4
    return res


def gp_nf(w, orders, commute):
    syl = [[g, (e % orders[g]) if orders[g] else e] for g, e in syllables(w)]
    syl = [s for s in syl if orders[s[0]] != 1 and s[1] != 0]

    def comm(g, h):
        return g == h or tuple(sorted((g, h))) in commute

    changed = True
    while changed:
        changed = False
        for i in range(len(syl)):
            for j in range(i + 1, len(syl)):
                if syl[j][0] == syl[i][0]:
                    g = syl[i][0]
                    e = syl[i][1] + syl[j][1]
                    if orders[g]:
                        e %= orders[g]
                    syl[i][1] = e
                    del syl[j]
                    if e == 0:
                        del syl[i]
                    changed = True
                    break
                if not comm(syl[j][0], syl[i][0]):
                    break
            if changed:
                break
    # Cartier-Foata normal form of the shuffle class
    rest = [tuple(s) for s in syl]
    layers = []
    while rest:
        layer, keep = [], []
        blocked = []
        for s in rest:
            if all(comm(s[0], b[0]) for b in blocked) and all(s[0] != t[0] for t in layer):
                layer.append(s)
            else:
                keep.append(s)
            blocked.append(s)
        layers.append(tuple(sorted(layer)))
        rest = keep
    return tuple(layers)


# ---------------------------------------------------------------- perturbations
def rule_bit(mu, bits):
    x = bits[0] | (bits[1] << 1) | (bits[2] << 2) | (bits[3] << 3)
    return (mu >> x) & 1


def build_instance(nf, g):
    flips = [(), g]
    fk = [nf(f) for f in flips]
    if fk[0] == fk[1]:
        return None
    outs = {}
    for f in flips:
        for m in MEMW:
            o = wmul(f, winv(m))
            outs.setdefault(nf(o), o)
    rows, ctxw = [], {}
    for ok_, o in outs.items():
        row = []
        for m in MEMW:
            s = wmul(o, m)
            k = nf(s)
            if k in fk:
                row.append(("F", fk.index(k)))
            else:
                ctxw.setdefault(k, s)
                row.append(("C", k))
        rows.append(row)
    return {"flips": flips, "outs": list(outs.values()), "rows": rows, "ctxw": ctxw}


def solutions(mu, inst, limit):
    rows = inst["rows"]
    order = sorted(range(len(rows)), key=lambda r: -len(set(rows[r])))
    sols, assign = [], {}

    def rec(t):
        if len(sols) >= limit:
            return
        if t == len(order):
            sols.append(dict(assign))
            return
        row = rows[order[t]]
        vs = list(dict.fromkeys(row))
        for vals in itertools.product((0, 1), repeat=len(vs)):
            loc = dict(zip(vs, vals))
            if any(v in assign and assign[v] != loc[v] for v in vs):
                continue
            before = [loc[v] for v in row]
            after = [1 - loc[v] if v[0] == "F" else loc[v] for v in row]
            if rule_bit(mu, before) != rule_bit(mu, after):
                continue
            new = [v for v in vs if v not in assign]
            for v in new:
                assign[v] = loc[v]
            rec(t + 1)
            for v in new:
                del assign[v]

    rec(0)
    return sols


def merges(inst, sol):
    ctx = [(inst["ctxw"][k], b) for (kind, k), b in sol.items() if kind == "C"]
    rels = set()
    for (u, bu), (v, bv) in itertools.combinations(ctx, 2):
        if bu != bv:
            rels.add(wmul(winv(u), v))
    for u, _ in ctx:
        for f in inst["flips"]:
            rels.add(wmul(winv(u), f))
    rels.add(wmul(winv(inst["flips"][0]), inst["flips"][1]))
    for u, v in itertools.combinations(inst["outs"], 2):
        rels.add(wmul(winv(u), v))
    rels.discard(())
    return sorted(rels)


def words_upto(n):
    out = [()]
    frontier = [()]
    for _ in range(n):
        nxt = []
        for w in frontier:
            for x in (1, -1, 2, -2, 3, -3):
                if w and w[-1] == -x:
                    continue
                nxt.append(w + (x,))
        out.extend(nxt)
        frontier = nxt
    return [w for w in out if w]


class Checker:
    def __init__(self, oracle, words, sol_limit=400, depth=1):
        self.o = oracle
        self.words = words
        self.sol_limit = sol_limit
        self.depth = depth
        self.memo = {}

    def classify(self, key):
        rec = self.o.get(key)
        res = recognize(rec)
        if res.get("form") == "unrecognized":
            res2 = recognize(self.o.get(key, tryfinite=True))
            if res2.get("amenable"):
                return res2
        return res

    def immediately_closed(self, key):
        c = self.classify(key)
        if c.get("amenable") is True:
            return {"closed": True, "why": c["form"]}
        if c.get("collapse"):
            return {"closed": True, "why": "memory-collapse(" + c["form"] + ")"}
        return {"closed": False, "form": c.get("form"), "has_nf": "nf" in c}

    def close(self, mu, key, depth, hint_words=()):
        mk = (mu, key, depth)
        if mk in self.memo:
            return self.memo[mk]
        imm = self.immediately_closed(key)
        if imm["closed"]:
            self.memo[mk] = {"closed": True, "why": imm["why"]}
            return self.memo[mk]
        c = self.classify(key)
        if "nf" not in c:
            self.memo[mk] = {"closed": False, "why": "no-normal-form", "form": c.get("form")}
            return self.memo[mk]
        nf = c["nf"]
        seen_words = []
        for g in list(hint_words) + self.words:
            if g in seen_words:
                continue
            seen_words.append(g)
            inst = build_instance(nf, g)
            if inst is None:
                continue
            sols = solutions(mu, inst, self.sol_limit)
            if not sols:
                continue
            ms = [(sol, merges(inst, sol)) for sol in sols]
            ms.sort(key=lambda t: len(t[1]))
            ext = {}
            for sol, rl in ms[:40]:
                for r in rl:
                    ext.setdefault(r, state_key(list(key) + [r]))
            self.o.batch(list(ext.values()))
            unrec = [k for k in ext.values() if recognize(self.o.get(k)).get("form") == "unrecognized"]
            if unrec:
                self.o.batch(unrec, tryfinite=True)
            for sol, rl in ms[:40]:
                certs, ok = [], True
                for r in rl:
                    ek = ext[r]
                    im = self.immediately_closed(ek)
                    if im["closed"]:
                        certs.append({"merge": list(r), "closed": im["why"]})
                        continue
                    if depth >= self.depth:
                        ok = False
                        break
                    child = self.close(mu, ek, depth + 1)
                    if not child["closed"]:
                        ok = False
                        break
                    certs.append({"merge": list(r), "child": child})
                if ok:
                    res = {"closed": True, "why": "perturbation", "flip": list(g),
                           "assignment": {json.dumps([kind, list(inst["ctxw"][k]) if kind == "C" else list(inst["flips"][k])]): b
                                          for (kind, k), b in sol.items()},
                           "merges": certs}
                    self.memo[mk] = res
                    return res
        self.memo[mk] = {"closed": False, "why": "no-certificate", "form": c.get("form")}
        return self.memo[mk]


GAP_LOWINDEX = r'''
F := FreeGroup(3);; FAM := FamilyObj(One(F));;
W := function(l) return AssocWordByLetterRep(FAM, l); end;;
OUT := OutputTextFile(OUTNAME, false);; SetPrintFormattingStatus(OUT, false);;
Low := function(key, rl, maxidx)
  local G, subs, U, act, n, imgs, res;
  G := F / List(rl, W);
  subs := LowIndexSubgroupsFpGroup(G, maxidx);
  res := [];
  for U in subs do
    n := Index(G, U);
    if n >= 3 then
      act := FactorCosetAction(G, U);
      imgs := List(GeneratorsOfGroup(G), g -> ListPerm(Image(act, g), n));
      Add(res, imgs);
    fi;
  od;
  AppendTo(OUT, "[\"", key, "\",", res, "]\n");
end;;
'''


def perm_mul(p, q):
    """Right action: x^(pq) = (x^p)^q, as for GAP permutations."""
    return tuple(q[p[i] - 1] for i in range(len(p)))


def perm_inv(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j - 1] = i + 1
    return tuple(out)


def eval_perm(w, gens):
    e = tuple(range(1, len(gens[0]) + 1))
    for x in w:
        g = gens[abs(x) - 1]
        e = perm_mul(e, g if x > 0 else perm_inv(g))
    return e


def audit_certificate(mu, cert, quotients):
    """End-to-end soundness check in finite quotients realizing the state: either a recorded merge
    holds in the quotient, or the perturbation is invisible there by direct evaluation."""
    stats = {"quotients": 0, "merge_holds": 0, "invisible": 0, "violations": 0}
    flip = tuple(cert["flip"])
    assign = {}
    for k, b in cert["assignment"].items():
        kind, w = json.loads(k)
        assign[(kind, tuple(w))] = b
    merge_words = [tuple(m["merge"]) for m in cert["merges"]]
    for gens in quotients:
        gens = [tuple(g) for g in gens]
        stats["quotients"] += 1
        if any(eval_perm(r, gens) == eval_perm((), gens) for r in merge_words):
            stats["merge_holds"] += 1
            continue
        x = {}
        for (kind, w), b in assign.items():
            x[eval_perm(w, gens)] = b
        flips = [eval_perm(f, gens) for f in ((), flip)]
        x2 = dict(x)
        for f in flips:
            x2[f] = 1 - x.get(f, 0)
        ok = True
        for f in ((), flip):
            for m in MEMW:
                o = wmul(f, winv(m))
                bits1 = [x.get(eval_perm(wmul(o, mm), gens), 0) for mm in MEMW]
                bits2 = [x2.get(eval_perm(wmul(o, mm), gens), 0) for mm in MEMW]
                if rule_bit(mu, bits1) != rule_bit(mu, bits2):
                    ok = False
        if ok:
            stats["invisible"] += 1
        else:
            stats["violations"] += 1
    return stats


def lowindex_quotients(gap, work, keys, maxidx=6):
    inp, outn = os.path.join(work, "low.g"), os.path.join(work, "low.out")
    with open(inp, "w") as fh:
        fh.write('OUTNAME := "%s";;\n' % outn)
        fh.write(GAP_LOWINDEX)
        for k in keys:
            sk = Oracle.skey(k)
            fh.write('Low("%s", %s, %d);;\n' % (sk.replace('"', '\\"'), json.dumps([list(r) for r in k]), maxidx))
        fh.write("CloseStream(OUT);; QUIT;\n")
    subprocess.run([gap, "-A", "-q", "-o", "8g", inp], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL, timeout=7200, check=False)
    got = {}
    if os.path.exists(outn):
        for line in open(outn):
            line = line.strip()
            if line:
                k, res = json.loads(line)
                got[k] = res
    return got


def collect_certs(node, key, out):
    if node.get("closed") and node.get("why") == "perturbation":
        out.append((key, node))
        for m in node["merges"]:
            if "child" in m:
                collect_certs(m["child"], state_key(list(key) + [tuple(m["merge"])]), out)


def main():
    flip1, tri, dfl, gap, work, mode = sys.argv[1:7]
    flip1, tri, dfl = json.load(open(flip1)), json.load(open(tri)), json.load(open(dfl))
    parts = flip1["partitions"]
    closed_prev = {str(x) for x in dfl["closed"]}
    oracle = Oracle(gap, work)
    if mode == "replay":
        rules = sorted(closed_prev, key=int)
        words = words_upto(2)
    else:
        rules = sorted((m for m in tri["survivors"] if m not in closed_prev), key=int)
        words = words_upto(3)
    checker = Checker(oracle, words, depth=int(os.environ.get("DEPTH", "1")))
    report = {"mode": mode, "rules": {}}
    n_closed = 0
    for mu_s in rules:
        mu = int(mu_s)
        branches, allc = {}, True
        for k in tri["survivors"][mu_s]:
            key = partition_relators(parts[int(k)])
            hints = []
            node = dfl["rules"].get(mu_s, {}).get("branches", {}).get(str(k), {})
            if node.get("flip"):
                hints.append(tuple(node["flip"]))
            res = checker.close(mu, key, 0, hints)
            branches[str(k)] = res
            if not res["closed"]:
                allc = False
        report["rules"][mu_s] = {"closed": allc, "branches": branches}
        n_closed += allc
        sys.stderr.write("rule %s closed=%s gapcalls=%d\n" % (mu_s, allc, oracle.calls))
        sys.stderr.flush()
    # end-to-end audit of every certificate in finite quotients (coset actions, index <= 6)
    certs = []
    for mu_s, rr in report["rules"].items():
        for k, node in rr["branches"].items():
            collect_certs(node, partition_relators(parts[int(k)]), certs)
    keys = list(dict.fromkeys(key for key, _ in certs))
    quots = lowindex_quotients(gap, work, keys, int(os.environ.get("AUDIT_INDEX", "6"))) if keys else {}
    audit = {"certificates": len(certs), "states": len(keys), "quotients": 0, "merge_holds": 0,
             "invisible": 0, "violations": 0}
    cert_rule = {}
    for mu_s, rr in report["rules"].items():
        for k, node in rr["branches"].items():
            sub = []
            collect_certs(node, partition_relators(parts[int(k)]), sub)
            for key, node2 in sub:
                cert_rule[id(node2)] = int(mu_s)
    for key, node in certs:
        st = audit_certificate(cert_rule[id(node)], node, quots.get(Oracle.skey(key), []))
        node["audit"] = st
        for f in ("quotients", "merge_holds", "invisible", "violations"):
            audit[f] += st[f]
    report["audit"] = audit
    report["summary"] = {"rules": len(rules), "closed": n_closed, "open": len(rules) - n_closed,
                         "gap_batches": oracle.calls, "depth": checker.depth, "audit": audit}
    json.dump(report, sys.stdout, default=str)
    sys.stderr.write(json.dumps(report["summary"]) + "\n")


if __name__ == "__main__":
    main()
