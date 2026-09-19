#!/usr/bin/env python3
"""Screen of same-point loop recursions over M_11 (node `same-point-loop-recursions-reduce-to-loop-graph-words`).

Points are coded 0..10 (the node's 1..11).  Rooted letters a = alpha, e = beta.
For each recursion the script
  1. checks (U) and (L1): every directed cycle of the weight-preserving digraph on signed state
     letters is a self-loop, at most one per letter;
  2. builds the loop graph Gamma_1 on X (edge r_s -> w_s labelled l_s = A s B for s|_x = A s B) and
     checks against Delta_2, Delta_3 that the level-n loop graphs are Gamma_1 on constant words
     (Lemma A and item 2 of the node);
  3. computes the cycle words of each component, their orders (exact finite order, or an
     infinite-order certificate), Q_E = section closure of the powers w^ord(w);
  4. runs the Kurosh test: a free basis in which every word of Q_E is conjugate into a block of
     letters with proper image, and the Whitehead-graph cut-vertex test (Stallings) for Q_E.
Run: nice -n 10 timeout 1200 python3 same_point_screen.py > same_point_screen.out
"""
import itertools, sys
sys.setrecursionlimit(10000)
from loopgraph import (N, ID, ALPHA, BETA, W, reduce, inv, fmt, pmul, pinv, Rec,
                       components)

ROOT = {"a": ALPHA, "e": BETA}

def group_order(gens):
    seen, todo = {ID}, [ID]
    while todo:
        p = todo.pop()
        for g in gens:
            q = pmul(p, g)
            if q not in seen: seen.add(q); todo.append(q)
    return len(seen)

def cyc(u):
    u = reduce(u)
    while len(u) >= 2 and u[0][0] == u[-1][0] and u[0][1] == -u[-1][1]: u = u[1:-1]
    return u
def canon(u):
    u = cyc(u)
    if not u: return u
    return min(u[i:] + u[:i] for i in range(len(u)))

def power_section_graph(R, w, cap=3000):
    """nodes: canonical cyclic words; edge u -> canon((u^l)|_x), weight l = length of the
    root cycle through x (one x per cycle)."""
    start = canon(w); nodes, edges, todo = {start}, {}, [start]
    while todo:
        u = todo.pop()
        if len(nodes) > cap: return None
        p, out, done = R.perm(u), [], set()
        for x in range(N):
            if x in done: continue
            cyc_x, y = [x], p[x]
            while y != x: cyc_x.append(y); y = p[y]
            done |= set(cyc_x)
            v = canon(R.sec(u * len(cyc_x), x)); out.append((v, len(cyc_x)))
            if v not in nodes: nodes.add(v); todo.append(v)
        edges[u] = out
    return start, nodes, edges

def infinite_order(R, w):
    """certificate: a strongly connected component, reachable from w, containing an edge of
    weight l > 1 (ord(u) >= l ord(u') along edges, so such a cycle forces infinite order)."""
    g = power_section_graph(R, w)
    if g is None: return None
    start, nodes, edges = g
    idx, low, st, on, comp, c = {}, {}, [], set(), {}, [0]
    def dfs(v):
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for u, _ in edges.get(v, []):
            if u not in idx: dfs(u); low[v] = min(low[v], low[u])
            elif u in on: low[v] = min(low[v], idx[u])
        if low[v] == idx[v]:
            while True:
                u = st.pop(); on.discard(u); comp[u] = v
                if u == v: break
    dfs(start)
    for v, out in edges.items():
        for u, l in out:
            if l > 1 and u and comp[u] == comp[v]: return (fmt(v), l, fmt(u))
    return False

from math import gcd
def lcm(a, b): return a * b // gcd(a, b)
def exact_order(R, w):
    """candidate order from the power-section graph (edges of weight 1 back into the current
    path are neutral), then certified exactly: w^o is trivial and w^(o/p) is not, p | o prime."""
    g = power_section_graph(R, w)
    if g is None: return None
    start, nodes, edges = g
    memo, path = {(): 1}, set()
    def rec(u):
        if u in memo: return memo[u]
        path.add(u); o = 1
        for v, l in edges[u]:
            o = lcm(o, l * (1 if v in path else rec(v)))
        path.discard(u); memo[u] = o; return o
    o = rec(start)
    if o > 100000 or not R.trivial(w * o): return None
    for p in {q for q in range(2, o + 1) if o % q == 0 and all(q % r for r in range(2, q))}:
        if R.trivial(w * (o // p)): return None
    return o

def wp_digraph(R):
    """weight-preserving digraph on signed state letters: (s,e) -x-> (t,f) if s^e|_x contains t^f"""
    E = []
    for s in R.states:
        for e in (1, -1):
            for x in range(N):
                u = R.lsec(s, e, x)
                for l, f in u:
                    if R.is_state(l): E.append(((s, e), x, (l, f)))
    return E

def check_L1(R):
    """(U) and (L1).  Returns (ok, loops) with loops[s] = (x, A, B) for s|_x = A s B."""
    if not R.unit_weight(): return False, "fails (U)"
    E = wp_digraph(R); V = {(s, e) for s in R.states for e in (1, -1)}
    adj = {v: [w for u, _, w in E if u == v and w != v] for v in V}
    # a non-self-loop cycle exists iff the digraph without self-loops has a cycle
    col = {v: 0 for v in V}
    def dfs(v):
        col[v] = 1
        for w in adj[v]:
            if col[w] == 1 or (col[w] == 0 and dfs(w)): return True
        col[v] = 2; return False
    if any(col[v] == 0 and dfs(v) for v in V): return False, "long cycle"
    loops = {}
    for s in R.states:
        xs = [x for u, x, w in E if u == (s, 1) and w == (s, 1)]
        if len(xs) > 1: return False, f"{s} loops at {xs}"
        if xs:
            u = R.lsec(s, 1, xs[0]); i = u.index((s, 1)); loops[s] = (xs[0], u[:i], u[i + 1:])
    return True, loops

def gamma1(R, loops):
    """edges r_s -> w_s of Gamma_1, with r_s = x^{A^-1}, w_s = x^{s B}"""
    out = []
    for s, (x, A, B) in loops.items():
        r = pinv(R.perm(A))[x]; w = R.perm(((s, 1),) + B)[x]
        out.append(((r,), (w,), A + ((s, 1),) + B, (s, 1, (x,))))
    return out

def delta_matches_gamma(R, loops, n):
    """Delta_n equals Gamma_1 placed on constant words (positive edges compared)"""
    D = sorted((i, o, l) for i, o, l, (s, e, y) in R.loop_graph(n) if e == 1)
    G = sorted((i * n, o * n, l) for i, o, l, _ in gamma1(R, loops))
    return D == G

def classify_components(R, loops):
    comps = components(gamma1(R, loops))
    return [(V, rk, base, cw) for V, E, rk, base, cw in comps]

def whitehead_graph(words, letters):
    """vertices letter^{+-}; for consecutive letters x y of a cyclic word, an edge x -- y^{-1}"""
    V = [(l, e) for l in letters for e in (1, -1)]
    E = set()
    for u in words:
        u = cyc(u)
        if not u: continue
        for k in range(len(u)):
            x, y = u[k], u[(k + 1) % len(u)]
            E.add(frozenset([x, (y[0], -y[1])]) if x != (y[0], -y[1]) else frozenset([x]))
    return V, E

def connected_without_cut_vertex(V, E):
    def conn(vs):
        vs = set(vs)
        if not vs: return True
        st, seen = [next(iter(vs))], set()
        while st:
            v = st.pop()
            if v in seen: continue
            seen.add(v)
            for ed in E:
                if v in ed:
                    for w in ed:
                        if w in vs and w not in seen: st.append(w)
        return seen == vs
    if not conn(V): return False
    return all(conn([w for w in V if w != v]) for v in V)

# ---------------- Kurosh test in Nielsen-adjusted bases ------------------------------------
def substitute(u, x, repl):
    out = []
    for l, e in u:
        out.extend(repl if (l, e) == (x, 1) else inv(repl) if (l, e) == (x, -1) else ((l, e),))
    return reduce(out)

def bounded_closed(R, loops, L):
    """the letters L are section-closed and each state letter in L has rooted non-loop sections:
    then <L> consists of bounded automorphisms (they form a group)"""
    for s in L:
        if s not in R.states: continue
        for x, u in R.states[s][1].items():
            if any(l not in L for l, _ in u): return False
            if (s not in loops or x != loops[s][0]) and R.weight(u) > 0: return False
    return True

def unbounded_witness(R, loops):
    """a looping letter s whose non-loop section contains a looping letter t that is not rooted
    (t has a non-loop section with nontrivial root).  Then t is nonfinitary (t|_{x_t^k} = C t D
    is never rooted) and s has >= n nontrivial sections at level n: s is unbounded."""
    def nonrooted(t):
        return any(R.perm(u) != ID for x, u in R.states[t][1].items() if x != loops[t][0])
    for s in loops:
        for x, u in R.states[s][1].items():
            if x == loops[s][0]: continue
            for l, _ in u:
                if l in loops and nonrooted(l): return (s, x, l)
    return None

def kurosh_blocks(R, loops, QE, cycle_words):
    """returns (killed, basis description, blocks).  Bases: loop-Nielsen s' = A s B (old s =
    A^-1 s' B^-1), then for each cycle word containing a state letter y exactly once, y -> that
    word.  In the final basis, words of QE are cyclically reduced and letters that co-occur are
    merged; a block is proper if it is one letter, or rooted, or its root image is not P, or
    the section closure of its letters is bounded while G has an unbounded letter."""
    defs = {l: ((l, 1),) for l in list(R.rooted) + list(R.states)}  # new letter -> old word
    words = [reduce(q) for q in QE]; cw = [reduce(c) for c in cycle_words]; desc = []
    for s, (x, A, B) in loops.items():
        n = s + "'"; repl = inv(A) + ((n, 1),) + inv(B)
        words = [substitute(q, s, repl) for q in words]; cw = [substitute(c, s, repl) for c in cw]
        defs[n] = A + ((s, 1),) + B; del defs[s]; desc.append(f"{n} = {fmt(defs[n])}")
    for c in cw:
        c = cyc(c)
        if len(c) <= 1: continue
        for y in {l for l, _ in c if l in defs and l not in R.rooted}:
            pos = [k for k, (l, _) in enumerate(c) if l == y]
            if len(pos) != 1: continue
            k = pos[0]; eps = c[k][1]; u, v = c[:k], c[k + 1:]
            n = "g" + str(len(desc)); ydef = inv(u) + ((n, 1),) + inv(v)
            ydef = ydef if eps == 1 else inv(ydef)
            words = [substitute(q, y, ydef) for q in words]
            cw = [substitute(z, y, ydef) for z in cw]
            defs[n] = reduce([t for l, e in c for t in (defs[l] if e == 1 else inv(defs[l]))])
            del defs[y]; desc.append(f"{n} = {fmt(defs[n])}")
            break
    par = {l: l for l in defs}
    def f(l):
        while par[l] != l: l = par[l]
        return l
    for q in words:
        ls = sorted({l for l, _ in cyc(q)})
        for l in ls[1:]: par[f(l)] = f(ls[0])
    blocks = {}
    for l in defs: blocks.setdefault(f(l), []).append(l)
    verdict = []
    unb = unbounded_witness(R, loops)
    for b in blocks.values():
        if len(b) == 1 or all(l in R.rooted for l in b): verdict.append((b, True)); continue
        perms = [R.perm(defs[l]) for l in b]
        if group_order(perms) < 7920: verdict.append((b, True)); continue
        L = {l for n in b for l, _ in defs[n]}
        while True:  # section closure of the letter set: <block> lies in <L>
            L2 = L | {l for s in L if s in R.states for u in R.states[s][1].values() for l, _ in u}
            if L2 == L: break
            L = L2
        verdict.append((b, bool(unb) and bounded_closed(R, loops, L)))
    return all(v for _, v in verdict), desc, verdict, words

def whitehead_filling(QE, letters):
    V, E = whitehead_graph(QE, letters)
    return connected_without_cut_vertex(V, E)

def bounded(R):
    """every letter section of a state letter at a non-loop point is rooted"""
    ok, loops = check_L1(R)
    for s, (perm, secs) in R.states.items():
        for x, u in secs.items():
            if (s not in loops or x != loops[s][0]) and R.weight(u) > 0: return False
    return True

def analyze(R, bound=240, verbose=False, check_delta=2):
    ok, loops = check_L1(R)
    if not ok: return {"class": "outside (L1)", "why": loops}
    res = {"loops": {s: (x, fmt(A), fmt(B)) for s, (x, A, B) in loops.items()}}
    if check_delta:
        res["Delta_n = Gamma_1 (n=2..%d)" % (check_delta + 1)] = all(
            delta_matches_gamma(R, loops, n) for n in range(2, check_delta + 2))
    comps = classify_components(R, loops)
    res["components"] = [(tuple(v[0] for v in V), rk, [fmt(c) for c in cw]) for V, rk, _, cw in comps if rk]
    # sanity: every cycle word u at its base c satisfies u|_c = u and c^u = c
    res["cycle words fixed by section at base"] = all(
        R.sec(c, base[0]) == c and R.perm(c)[base[0]] == base[0] for V, rk, base, cw in comps for c in cw)
    res["bounded"] = bounded(R)
    maxrank = max([rk for _, rk, _, _ in comps] + [0])
    if maxrank >= 2:
        res["class"] = "BOUQUET (rank >= 2 loop group)"
        if res["bounded"]: res["verdict"] = "not fp (bounded, hence contracting regular branch)"
        else: res["verdict"] = "open: reduces to the ray-loop subgroup at the bouquet ray"
        return res
    if res["bounded"] and maxrank < 2:
        res["class"] = "TREE" if maxrank == 0 else "RANK-ONE"
        res["verdict"] = "not fp (bounded, hence contracting regular branch)"; return res
    if maxrank == 0:
        res["class"] = "TREE"; res["verdict"] = "not fp (Q^infinity empty)"; return res
    cws = [c for _, rk, _, cw in comps for c in cw]
    orders = {}
    for c in cws:
        cert = infinite_order(R, c)
        if cert: orders[fmt(c)] = ("infinite", cert); continue
        o = exact_order(R, c) or R.order(c, bound)
        orders[fmt(c)] = ("finite", o) if o else ("unknown", None)
    res["orders"] = orders
    res["class"] = "RANK-ONE"
    fin = [(c, orders[fmt(c)][1]) for c in cws if orders[fmt(c)][0] == "finite"]
    if any(orders[fmt(c)][0] == "unknown" for c in cws):
        res["verdict"] = "undecided (an order is not certified)"; return res
    if not fin:
        res["verdict"] = "not fp (every cycle word has infinite order, so Q^infinity is empty)"
        return res
    QE = R.closure([c * o for c, o in fin])
    res["|Q_E|"] = len(QE)
    killed, desc, verdict, words = kurosh_blocks(R, loops, QE, cws)
    res["basis"] = desc
    res["blocks"] = [(b, "proper" if v else "image not known proper") for b, v in verdict]
    letters = list(R.rooted) + list(R.states)
    res["Whitehead graph of Q_E connected without cut vertex"] = whitehead_filling(QE, letters)
    if killed: res["verdict"] = "not fp (Kurosh: Q_E carried by a free splitting with proper images)"
    else:
        res["verdict"] = "SURVIVOR: fp iff <S | Q_E, s = T_k(s)> presents G for some k"
        res["Q_E sample"] = sorted((fmt(q) for q in QE), key=len)[:8]
    return res

def show(name, res):
    print("===", name)
    for k, v in res.items(): print(f"  {k}: {v}")

# ---------------- the family ------------------------------------------------------------------
PERMWORDS = ["a", "e", "a e", "a E", "A e", "e a", "a a", "e e"]
DECOS = ["", "a", "A", "e", "E"]
def family(linear):
    base = Rec("", ROOT, {})
    for ws, wt in itertools.product(PERMWORDS, repeat=2):
        ps, pt = base.perm(W(ws)), base.perm(W(wt))
        if group_order([ps, pt]) != 7920: continue
        for As, Bs, At, Bt in itertools.product(DECOS, repeat=4):
            ssec = {0: W(" ".join(filter(None, [As, "s", Bs]))), 1: W("a"), 2: W("e")}
            if linear: ssec[3] = W("t")
            tsec = {0: W(" ".join(filter(None, [At, "t", Bt]))), 4: W("a")}
            name = f"pi_s={ws} pi_t={wt} s|0={fmt(ssec[0])} t|0={fmt(tsec[0])}" + (" s|3=t" if linear else "")
            yield name, Rec(name, ROOT, {"s": (ps, ssec), "t": (pt, tsec)})

def calibrate():
    I = ID
    cases = [
        ("R'' (bouquet at 0; killed by the ray-loop obstruction)", {"b": (I, {0: W("b"), 1: W("a"), 2: W("e")}), "c": (I, {0: W("c"), 1: W("b a")})}),
        ("R' (separated loops)", {"b": (I, {0: W("b"), 1: W("a"), 2: W("e")}), "c": (I, {3: W("c"), 4: W("b a")})}),
        ("R_0 = <M_11, b> (one loop)", {"b": (I, {0: W("b"), 1: W("a"), 2: W("e")})}),
        ("R° (C loops at two points: outside (L1))", {"b": (I, {0: W("b"), 1: W("a"), 2: W("e")}), "c": (I, {3: W("c"), 4: W("b a"), 5: W("C")})}),
    ]
    for name, st in cases: show(name, analyze(Rec(name, ROOT, st)))

if __name__ == "__main__":
    calibrate()
    for linear in (False, True):
        tally, examples = {}, {}
        for name, R in family(linear):
            res = analyze(R, check_delta=1 if linear else 0)
            key = (res["class"], res["verdict"]); tally[key] = tally.get(key, 0) + 1
            if "Delta_n = Gamma_1 (n=2..2)" in res and not res["Delta_n = Gamma_1 (n=2..2)"]:
                print("DELTA MISMATCH", name)
            if not res["cycle words fixed by section at base"]: print("FIX MISMATCH", name)
            examples.setdefault(key, []).append((name, res))
        print(f"\n##### family linear={linear}: s|0 = A s B, s|1 = alpha, s|2 = beta"
              + (", s|3 = t" if linear else "") + "; t|0 = C t D, t|4 = alpha")
        for key, n in sorted(tally.items(), key=lambda kv: -kv[1]): print(f"  {n:6d}  {key[0]}  ->  {key[1]}")
        for key, ex in examples.items():
            for name, res in ex[:2 if ("SURVIVOR" in key[1] or "open" in key[1]
                                      or "undecided" in key[1] or "Kurosh" in key[1]) else 0]:
                show(name, res)
