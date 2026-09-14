#!/usr/bin/env python3
"""fsac.py -- lane hl-andrews-curtis.
Independent Python model of cellular fake surfaces (per-edge sheet bijections), disk words after
collapsing a spanning tree, a greedy stable Andrews-Curtis trivializer that emits a macro certificate,
and an independent certificate verifier.

Certificate macros (each is a composite of (AC1)-(AC5)):
  ["conj", i, u]        r_i <- u r_i u^-1                  (AC3 letter by letter)
  ["mulc", j, i, u, s]  r_j <- r_j (u r_i^s u^-1), j != i  (AC3 on r_i, AC2 if s=-1, AC1, then undo)
  ["inv", i]            r_i <- r_i^-1                      (AC2)
  ["destab", g]         some r_k == [g], g occurs in no other relator: delete r_k and g  (AC5)
A certificate is valid when replay ends with no relators and no generators.
"""
import itertools, json, sys, collections
from fractions import Fraction

P = [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]

def graphs(t):
    pos = [(i,j) for i in range(t) for j in range(i,t)]
    A = [[0]*t for _ in range(t)]; rs = [0]*t; canon = set()
    def rec(p):
        if p == len(pos):
            if any(r != 4 for r in rs): return
            seen = {0}; st = [0]
            while st:
                u = st.pop()
                for w in range(t):
                    if A[u][w] and w not in seen: seen.add(w); st.append(w)
            if len(seen) != t: return
            best = max(tuple(A[q[i]][q[j]] for i in range(t) for j in range(t)) for q in itertools.permutations(range(t)))
            canon.add(best); return
        i, j = pos[p]
        if j == i and i > 0 and rs[i-1] != 4: return
        for x in range(5):
            if i == j:
                if x % 2 or rs[i] + x > 4: continue
                A[i][i] = x; rs[i] += x; rec(p+1); rs[i] -= x; A[i][i] = 0
            else:
                if rs[i] + x > 4 or rs[j] + x > 4: continue
                A[i][j] = A[j][i] = x; rs[i] += x; rs[j] += x; rec(p+1); rs[i] -= x; rs[j] -= x; A[i][j] = A[j][i] = 0
    rec(0)
    return [[list(c[i*t:(i+1)*t]) for i in range(t)] for c in sorted(canon, reverse=True)]

def load_graphs(t):
    import os
    fn = f"graphs-t{t}.json"
    if os.path.exists(fn): return json.load(open(fn))
    gs = graphs(t); json.dump(gs, open(fn, "w")); return gs

class Surface:
    def __init__(self, A):
        t = len(A); self.t = t
        vert = []
        for i in range(t):
            for j in range(i, t):
                m = A[i][i]//2 if i == j else A[i][j]
                for _ in range(m): vert += [i, j]
        self.vert = vert; H = len(vert); self.E = H//2
        self.oth = [[x for x in range(H) if x != h and vert[x] == vert[h]] for h in range(H)]
        tree = set(); seen = {0}; grew = True
        while grew:
            grew = False
            for e in range(self.E):
                u, w = vert[2*e], vert[2*e+1]
                if u != w and ((u in seen) != (w in seen)): seen |= {u, w}; tree.add(e); grew = True
        self.set_tree(tree)
    def set_tree(self, tree):
        self.tree = set(tree); self.gen = {}; c = 0
        for e in range(self.E):
            if e not in self.tree: c += 1; self.gen[e] = c
    def spanning_trees(self):
        t = self.t; nonloop = [e for e in range(self.E) if self.vert[2*e] != self.vert[2*e+1]]
        for T in itertools.combinations(nonloop, t-1):
            parent = list(range(t)); ok = True
            def find(x):
                while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
                return x
            for e in T:
                a, b = find(self.vert[2*e]), find(self.vert[2*e+1])
                if a == b: ok = False; break
                parent[a] = b
            if ok: yield list(T)
    def words(self, code):
        nxt = {}
        for e in range(self.E):
            d = code % 6; code //= 6
            for k in range(3): nxt[(2*e, k)] = (2*e+1, P[d][k]); nxt[(2*e+1, P[d][k])] = (2*e, k)
        def step(h, x):          # exit via h having entered from x
            h2, k2 = nxt[(h, self.oth[h].index(x))]; y = self.oth[h2][k2]; return (y, h2)
        seen = set(); disks = []
        for h in range(len(self.vert)):
            for x in self.oth[h]:
                if (h, x) in seen: continue
                s = (h, x); c = s; w = []
                while True:
                    seen.add(c); seen.add((c[1], c[0])); e = c[0] >> 1
                    w.append((e+1) if c[0] % 2 == 0 else -(e+1)); c = step(*c)
                    if c == s: break
                disks.append(w)
        return disks
    def presentation(self, code):
        disks = self.words(code)
        rels = [freered([(1 if a > 0 else -1)*self.gen[abs(a)-1] for a in w if abs(a)-1 in self.gen]) for w in disks]
        return disks, rels

def a5():
    els = [p for p in itertools.permutations(range(5))
           if sum(1 for i in range(5) for j in range(i+1, 5) if p[i] > p[j]) % 2 == 0]
    return els
def pmul(p, q): return tuple(p[q[i]] for i in range(len(q)))
def pinv(p):
    r = [0]*len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)
def evalw(w, img, e):
    acc = e
    for a in w: acc = pmul(acc, img[abs(a)] if a > 0 else pinv(img[abs(a)]))
    return acc
def hom_to_a5(rels, n):
    """A nontrivial homomorphism to A_5 from a perfect group is onto (A_5 is simple and its only perfect
    subgroups are 1 and A_5), so it certifies a nontrivial fundamental group. Returns images or None."""
    els = a5(); e = tuple(range(5)); order = []; rem = [set(abs(a) for a in r) for r in rels]
    while len(order) < n:   # order generators so that relators close early
        best = max((g for g in range(1, n+1) if g not in order),
                   key=lambda g: sum(1 for s in rem if s and s <= set(order) | {g}))
        order.append(best)
    check = {g: [] for g in order}
    for r in rels:
        if r: check[max(r, key=lambda a: order.index(abs(a))) and order[max(order.index(abs(a)) for a in r)]].append(r)
    img = {}
    classes = [(0,1,2,3,4), (1,0,3,2,4), (1,2,0,3,4), (1,2,3,4,0), (2,3,4,0,1)]   # A_5 classes: 1, (01)(23), (012), x=(01234), x^2
    def rec(k, nontriv):
        if k == n: return dict(img) if nontriv else None
        g = order[k]
        for x in (classes if k == 0 else els):
            img[g] = x
            if all(evalw(r, img, e) == e for r in check[g]):
                res = rec(k+1, nontriv or x != e)
                if res: return res
        del img[g]; return None
    return rec(0, False)

def freered(w):
    out = []
    for a in w:
        if out and out[-1] == -a: out.pop()
        else: out.append(a)
    return out
def inv(w): return [-a for a in reversed(w)]

def det_pm1(rels, n):
    if len(rels) != n: return False
    M = [[Fraction(0)]*n for _ in range(n)]
    for i, r in enumerate(rels):
        for a in r: M[i][abs(a)-1] += 1 if a > 0 else -1
    d = Fraction(1)
    for k in range(n):
        p = next((r for r in range(k, n) if M[r][k] != 0), None)
        if p is None: return False
        if p != k: M[k], M[p] = M[p], M[k]; d = -d
        d *= M[k][k]
        for r in range(k+1, n):
            f = M[r][k] / M[k][k]
            for c in range(k, n): M[r][c] -= f*M[k][c]
    return abs(d) == 1

def apply(R, gens, mv):
    op = mv[0]
    if op == "conj":
        _, i, u = mv; R[i] = freered(u + R[i] + inv(u))
    elif op == "mulc":
        _, j, i, u, s = mv
        assert i != j and s in (1, -1) and i in R and j in R
        R[j] = freered(R[j] + u + (R[i] if s == 1 else inv(R[i])) + inv(u))
    elif op == "inv":
        _, i = mv; R[i] = freered(inv(R[i]))
    elif op == "destab":
        _, g = mv
        ks = [k for k in R if R[k] == [g]]
        assert ks and g in gens
        k = ks[0]
        assert all(g not in R[m] and -g not in R[m] for m in R if m != k)
        del R[k]; gens.discard(g)
    else: raise ValueError(op)
    for k in R: assert all(abs(a) in gens for a in R[k]), "letter outside generating set"

def verify(rels, n, cert):
    R = {i: list(r) for i, r in enumerate(rels)}; gens = set(range(1, n+1))
    try:
        for mv in cert: apply(R, gens, mv)
    except AssertionError:
        return False
    return not R and not gens

def trivialize(rels, n):
    R = {i: list(r) for i, r in enumerate(rels)}; cert = []
    def emit(mv): cert.append(mv); apply(R, set(range(1, n+1)), mv)
    def rec(idx, gset):
        if not idx: return True
        cand = []
        for i in idx:
            for g in gset:
                if sum(1 for a in R[i] if abs(a) == g) == 1: cand.append((len(R[i]), i, g))
        if not cand: return False
        _, i, g = min(cand)
        if -g in R[i]: emit(["inv", i])     # make the unique occurrence +g, then rotate it to the front
        p = R[i].index(g)
        emit(["conj", i, inv(R[i][:p])])
        assert R[i][0] == g and sum(1 for a in R[i] if abs(a) == g) == 1
        for j in idx:
            if j == i: continue
            while any(abs(a) == g for a in R[j]):
                q = next(k for k, a in enumerate(R[j]) if abs(a) == g); b = R[j][q+1:]
                if R[j][q] == g: emit(["mulc", j, i, inv(b) + [-g], -1])
                else: emit(["mulc", j, i, inv(b), 1])
        if not rec([j for j in idx if j != i], gset - {g}): return False
        single = {abs(R[j][0]): j for j in idx if j != i}
        while len(R[i]) > 1:
            x = R[i][-1]; c = []            # remove the last letter x using r_k = [+-|x|]
            k = single[abs(x)]; sgn = R[k][0] // abs(x)
            emit(["mulc", i, k, inv(c), -1 if sgn*(1 if x > 0 else -1) == 1 else 1])
        return True
    if not rec(list(R), set(range(1, n+1))): return None
    for k in list(R):
        if R[k][0] < 0: emit(["inv", k])
    for g in range(1, n+1): emit(["destab", g])
    return cert

def zopen(fn, mode="r"):
    import gzip, builtins
    return gzip.open(fn, mode + "t") if fn.endswith(".gz") else builtins.open(fn, mode)

def canon_cyclic(w):
    w = list(w)
    while len(w) > 1 and w[0] == -w[-1]: w = w[1:-1]
    if not w: return ()
    cands = []
    for x in (w, inv(w)):
        for p in range(len(x)): cands.append(tuple(x[p:] + x[:p]))
    return min(cands)

def bfs_unstick(R, idx, gset, n, max_states=30000, extra_len=6):
    """Breadth-first search over cancelling product moves on the relators idx until some generator of gset
    occurs exactly once in some relator. Returns (new relators on idx, moves) or None."""
    from collections import deque
    start = {k: list(R[k]) for k in idx}; L0 = sum(len(v) for v in start.values())
    key = lambda S: tuple(sorted(canon_cyclic(S[k]) for k in idx))
    unstuck = lambda S: any(sum(1 for a in S[i] if abs(a) == g) == 1 for i in idx for g in gset)
    Q = deque([(start, [])]); seen = {key(start)}
    while Q and len(seen) < max_states:
        S, mv = Q.popleft()
        for j in idx:
            rj = S[j]
            for q in range(max(1, len(rj))):
                rjr = rj[q:] + rj[:q]
                for i in idx:
                    if i == j: continue
                    for s in (1, -1):
                        ri = S[i] if s == 1 else inv(S[i])
                        for p in range(len(ri)):
                            rot = ri[p:] + ri[:p]
                            if not (rjr and rot and rjr[-1] == -rot[0]): continue
                            T = {k: list(v) for k, v in S.items()}; moves = list(mv)
                            if q: moves.append(["conj", j, inv(rj[:q])]); T[j] = freered(inv(rj[:q]) + T[j] + rj[:q])
                            u = inv(ri[:p]); moves.append(["mulc", j, i, u, s])
                            T[j] = freered(T[j] + u + (T[i] if s == 1 else inv(T[i])) + inv(u))
                            if not T[j] or sum(len(v) for v in T.values()) > L0 + extra_len: continue
                            kk = key(T)
                            if kk in seen: continue
                            seen.add(kk)
                            if unstuck(T): return T, moves
                            Q.append((T, moves))
    return None

def trivialize_dfs(rels, n, budget=5000, branch=4):
    """Backtracking version of trivialize: tries up to `branch` eliminations at each node; when no generator
    occurs exactly once, a bounded breadth-first product search unsticks the node."""
    count = [0]
    def elim(R, idx, gset):
        if not idx: return []
        count[0] += 1
        if count[0] > budget: return None
        cand = sorted((len(R[i]), i, g) for i in idx for g in gset if sum(1 for a in R[i] if abs(a) == g) == 1)
        if not cand:
            res = bfs_unstick(R, idx, gset, n)
            if res is None: return None
            T, mv = res; R2 = {k: list(v) for k, v in R.items()}; R2.update(T)
            sub = elim(R2, idx, gset)
            if sub is None: return None
            R.clear(); R.update(R2)
            return mv + sub
        for _, i, g in cand[:branch]:
            R2 = {k: list(v) for k, v in R.items()}; moves = []
            def emit(mv, R2=R2, moves=moves): moves.append(mv); apply(R2, set(range(1, n+1)), mv)
            if -g in R2[i]: emit(["inv", i])
            p = R2[i].index(g); emit(["conj", i, inv(R2[i][:p])])
            for j in idx:
                if j == i: continue
                while any(abs(a) == g for a in R2[j]):
                    q = next(k for k, a in enumerate(R2[j]) if abs(a) == g); b = R2[j][q+1:]
                    if R2[j][q] == g: emit(["mulc", j, i, inv(b) + [-g], -1])
                    else: emit(["mulc", j, i, inv(b), 1])
            sub = elim(R2, [j for j in idx if j != i], gset - {g})
            if sub is None: continue
            moves += sub
            single = {abs(R2[j][0]): j for j in idx if j != i}
            while len(R2[i]) > 1:
                x = R2[i][-1]; k = single[abs(x)]; sgn = R2[k][0] // abs(x)
                emit(["mulc", i, k, [], -1 if sgn*(1 if x > 0 else -1) == 1 else 1])
            R.clear(); R.update(R2)
            return moves
        return None
    R = {i: list(r) for i, r in enumerate(rels)}
    moves = elim(R, list(R), set(range(1, n+1)))
    if moves is None: return None
    for k in list(R):
        if R[k][0] < 0: moves.append(["inv", k]); R[k] = inv(R[k])
    for g in range(1, n+1): moves.append(["destab", g])
    return moves

def todd_coxeter(rels, n, limit=200000):
    """HLT coset enumeration over the trivial subgroup. Returns (order, table of live cosets) or None."""
    ng = 2*n
    code = lambda a: 2*(a-1) if a > 0 else 2*(-a-1)+1
    Rw = [[code(a) for a in r] for r in rels if r]
    tab, rep = [], []
    def define(c, x):
        d = len(tab); tab.append([-1]*ng); rep.append(d); tab[c][x] = d; tab[d][x ^ 1] = c; return d
    def find(c):
        while rep[c] != c: rep[c] = rep[rep[c]]; c = rep[c]
        return c
    def coincidence(a, b):
        q = []
        def merge(k, l):
            k, l = find(k), find(l)
            if k == l: return
            if k > l: k, l = l, k
            rep[l] = k; q.append(l)
        merge(a, b); i = 0
        while i < len(q):
            e = q[i]; i += 1
            for x in range(ng):
                f = tab[e][x]
                if f == -1: continue
                if tab[f][x ^ 1] == e: tab[f][x ^ 1] = -1
                e1, f1 = find(e), find(f)
                if tab[e1][x] != -1: merge(f1, tab[e1][x])
                elif tab[f1][x ^ 1] != -1: merge(e1, tab[f1][x ^ 1])
                else: tab[e1][x] = f1; tab[f1][x ^ 1] = e1
    def scan_fill(c, w):
        f, b, i, j = c, c, 0, len(w) - 1
        while True:
            while i <= j and tab[f][w[i]] != -1: f = tab[f][w[i]]; i += 1
            if i > j:
                if f != b: coincidence(f, b)
                return
            while j >= i and tab[b][w[j] ^ 1] != -1: b = tab[b][w[j] ^ 1]; j -= 1
            if j < i: coincidence(f, b); return
            if i == j: tab[f][w[i]] = b; tab[b][w[i] ^ 1] = f; return
            define(f, w[i])
            if len(tab) > limit: raise OverflowError
    tab.append([-1]*ng); rep.append(0); c = 0
    try:
        while c < len(tab):
            if rep[c] == c:
                for w in Rw:
                    scan_fill(c, w)
                    if rep[c] != c: break
                for x in range(ng):
                    if rep[c] == c and tab[c][x] == -1: define(c, x)
            c += 1
    except OverflowError:
        return None
    live = [k for k in range(len(tab)) if rep[k] == k]; pos = {k: i for i, k in enumerate(live)}
    images = {g: [pos[find(tab[k][code(g)])] for k in live] for g in range(1, n+1)}
    return len(live), images

def perm_certificate_ok(rels, n, images):
    N = len(images[1]); ident = list(range(N))
    for g in range(1, n+1):
        if sorted(images[g]) != ident: return False
    inv_img = {g: [0]*N for g in images}
    for g in images:
        for p, q in enumerate(images[g]): inv_img[g][q] = p
    for r in rels:
        for p in range(N):
            q = p
            for a in r: q = images[a][q] if a > 0 else inv_img[-a][q]
            if q != p: return False
    return any(images[g] != ident for g in images)

if __name__ == "__main__":
    mode, fn = sys.argv[1], sys.argv[2]
    open = zopen
    if mode == "graphs":
        for gi, A in enumerate(graphs(int(fn)), 1): print(gi, json.dumps(A))
    elif mode == "certify":             # certify <classes file> <out jsonl> <shard> <nshards>
        out = open(sys.argv[3], "w"); shard, ns = int(sys.argv[4]), int(sys.argv[5])
        cache = {}; stats = {"ok": 0, "stuck": 0, "badmodel": 0}
        for ln, line in enumerate(open(fn)):
            if ln % ns != shard: continue
            t, gi, code, ml = map(int, line.split())
            if t not in cache: cache[t] = [Surface(A) for A in load_graphs(t)]
            S = cache[t][gi-1]; disks, rels = S.presentation(code); n = t+1
            if len(disks) != n or not det_pm1(rels, n) or min(map(len, disks)) != ml:
                stats["badmodel"] += 1; out.write(json.dumps({"t": t, "g": gi, "code": code, "status": "badmodel"})+"\n"); continue
            cert = trivialize(rels, n)
            if cert is not None and verify(rels, n, cert):
                stats["ok"] += 1; out.write(json.dumps({"t": t, "g": gi, "code": code, "rels": rels, "cert": cert})+"\n")
            else:
                stats["stuck"] += 1; out.write(json.dumps({"t": t, "g": gi, "code": code, "rels": rels, "status": "stuck"})+"\n")
        print(json.dumps(stats))
    elif mode == "rescue":              # rescue <stuck jsonl glob> <out jsonl>: other trees, then A_5 images
        import glob
        out = open(sys.argv[3], "w"); cache = {}; stats = collections.Counter()
        for f in sorted(glob.glob(fn)):
            for line in open(f):
                d = json.loads(line)
                if d.get("status") != "stuck": continue
                t, gi, code = d["t"], d["g"], d["code"]; n = t+1
                if t not in cache: cache[t] = [Surface(A) for A in load_graphs(t)]
                S = cache[t][gi-1]; done = False
                for T in S.spanning_trees():
                    S.set_tree(T); _, rels = S.presentation(code)
                    cert = trivialize(rels, n)
                    if cert is not None and verify(rels, n, cert):
                        out.write(json.dumps({"t": t, "g": gi, "code": code, "tree": T, "rels": rels, "cert": cert})+"\n")
                        stats["ok_other_tree"] += 1; done = True; break
                if not done:
                    rels = d["rels"]; img = hom_to_a5(rels, n)
                    if img and all(evalw(r, img, tuple(range(5))) == tuple(range(5)) for r in rels):
                        out.write(json.dumps({"t": t, "g": gi, "code": code, "rels": rels, "a5": {str(k): v for k, v in img.items()}})+"\n")
                        stats["pi1_nontrivial_a5"] += 1
                    else:
                        out.write(json.dumps({"t": t, "g": gi, "code": code, "rels": rels, "status": "open"})+"\n")
                        stats["open"] += 1
                out.flush()
        print(json.dumps(stats))
    elif mode == "rescue2":             # rescue2 <open jsonl glob> <out jsonl>: backtracking on every tree, then coset enumeration
        import glob
        out = open(sys.argv[3], "w"); cache = {}; stats = collections.Counter()
        for f in sorted(glob.glob(fn)):
            for line in open(f):
                d = json.loads(line)
                if d.get("status") not in ("open", "trivial-group-no-certificate"): continue
                t, gi, code = d["t"], d["g"], d["code"]; n = t+1
                if t not in cache: cache[t] = [Surface(A) for A in load_graphs(t)]
                S = cache[t][gi-1]; rec_out = None
                for T in S.spanning_trees():
                    S.set_tree(T); _, rels = S.presentation(code)
                    cert = trivialize_dfs(rels, n)
                    if cert is not None and verify(rels, n, cert):
                        rec_out = {"t": t, "g": gi, "code": code, "tree": T, "rels": rels, "cert": cert}; stats["ok_dfs"] += 1; break
                if rec_out is None:
                    res = todd_coxeter(d["rels"], n)
                    if res is None: rec_out = dict(d, status="unresolved"); stats["unresolved"] += 1
                    elif res[0] == 1: rec_out = dict(d, status="trivial-group-no-certificate"); stats["trivial_no_cert"] += 1
                    elif perm_certificate_ok(d["rels"], n, res[1]):
                        rec_out = {"t": t, "g": gi, "code": code, "rels": d["rels"], "order": res[0],
                                   "perm": {str(k): v for k, v in res[1].items()}}; stats["pi1_finite_nontrivial"] += 1
                    else: rec_out = dict(d, status="tc-check-failed"); stats["tc_check_failed"] += 1
                out.write(json.dumps(rec_out) + "\n"); out.flush()
        print(json.dumps(stats))
