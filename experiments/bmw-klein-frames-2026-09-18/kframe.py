# Conjugate-frame Klein-chain search for BMW parity kernels (census patterns mpA_npB, transposed letters allowed).
# Theorem 4 of bmw-census-klein-power-chain-certificates: every Klein pair (y inverts x) is conjugate to a pure pair.
# So every node x of a Klein chain carries a FRAME x = c W c^-1 with W a cyclically reduced pure word (a V-word or an
# H-word).  The inverters of W are exactly W^2j p A p^-1, p = W[:i] a prefix (vertex p.Q on the axis of W), A a pure
# word of the other family inverting the rotation R_i = p^-1 W p (it fixes that vertex).  Hence the K-moves
#     x = c W c^-1  ->  y = c p A p^-1 c^-1          (y inverts x, so |x| < |y|; frame of y: (c p u, A'), A = u A' u^-1)
# and the power moves x = c r^e c^-1 -> c r^f c^-1 (f > e, r an even root; |x| <= |y|) generate every Klein chain
# whose pure inverters have length <= L (and shift j = 0, or |j| <= 1 with --shift).  Nodes are elements of Gamma^+
# up to inversion, keyed by normal form; the search is a BFS from all cyclically reduced pure seeds of length <= S
# up to normal-form length NB; a strongly connected component containing a K edge yields a certificate cycle.
# Conjugating by c is conjugation by an element fixing the vertex c.Q (resp. c.P) of one tree: no ball is enumerated.
# usage: kframe.py census.json classes|cand L S NB [--cand out_X.jsonl] [--skip chains.json] [--cap N] [--shift]
#        [--out chains_new.json] [--log log.jsonl] [--sb SB]
# --sb SB adds as seeds every B with |B| <= SB inverted by a pure A with |A| <= L (all flat Klein bottles of that size).
import sys, json
from collections import deque
sys.setrecursionlimit(100000)
A_ = sys.argv
D = json.load(open(A_[1])); sel = A_[2]; L, S, NB = int(A_[3]), int(A_[4]), int(A_[5])
def opt(k, d=None): return A_[A_.index(k) + 1] if k in A_ else d
CAP = int(opt('--cap', 200000)); SHIFT = '--shift' in A_; SB = int(opt('--sb', 0))
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
INV = {'h': iA, 'v': iB}
if sel == 'cand':
    recs = [json.loads(l) for l in open(opt('--cand'))]
    todo = [r['idx'] for r in recs if r.get('finH') is None or r.get('finV') is None]
else: todo = [int(c) for c in sel.split(',')]
if opt('--skip'):
    sk = set(int(k) for k in json.load(open(opt('--skip'))))
    todo = [c for c in todo if c not in sk]
OUT = opt('--out'); LOG = None
if opt('--log'):                       # resumable: skip classes already logged with the same parameters
    try:
        done = set(r['class'] for r in map(json.loads, open(opt('--log'))) if (r['L'], r['S'], r['NB'], r.get('SB', 0), r['shift']) == (L, S, NB, SB, SHIFT))
        todo = [c for c in todo if c not in done]
    except FileNotFoundError: pass
    LOG = open(opt('--log'), 'a')
def red(w, inv):                       # free reduction of a word over one family
    o = []
    for c in w:
        if o and o[-1] == inv[c]: o.pop()
        else: o.append(c)
    return tuple(o)
def winv(w, inv): return tuple(inv[c] for c in reversed(w))
def fmt(g): return 'v' + ''.join(map(str, g[0])) + '|h' + ''.join(map(str, g[1]))
def run(ci, cap):
    SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}          # (h, v) -> (v', h'):  h v = v' h'
    VH = {}
    for (h, v), (v2, h2) in SQ.items(): VH[(iB[v2], h)] = (h2, iB[v])
    def mul(g1, g2):
        V1, H1 = g1; V2, H2 = g2; H = list(H1); Vo = []
        for v in V2:                                           # H v = v' H'
            for i in range(len(H) - 1, -1, -1):
                v, H[i] = SQ[(H[i], v)]
            Vo.append(v)
        return red(V1 + tuple(Vo), iB), red(tuple(H) + H2, iA)
    def inv(g): return mul(((), winv(g[1], iA)), (winv(g[0], iB), ()))
    def el(f, w): return (tuple(w), ()) if f == 'v' else ((), tuple(w))
    def key(g):
        gi = inv(g); return min(g, gi)
    def fixed(x, T, alpha, invl):     # reduced words a (len <= L, even) with x a = a x'; returns (a, x')
        res = []
        def dfs(a, sec):
            if a and len(a) % 2 == 0: res.append((a, tuple(sec)))
            if len(a) == L: return
            for c in range(alpha):
                if a and a[-1] == invl[c]: continue
                s = list(sec); y = c
                for i in range(len(s) - 1, -1, -1):
                    y, s[i] = T[(s[i], y)]
                if y == c: dfs(a + (c,), s)
        dfs((), x); return res
    PC = {}
    def pinv(f, W):                    # pure words A of the other family with A W A^-1 = W^-1, |A| <= L
        k = (f, W)
        if k not in PC:
            if f == 'h':
                PC[k] = [a for a, s in fixed(winv(W, iA), SQ, n, iB) if s == W]
            else:
                Wi = winv(W, iB)
                PC[k] = [winv(c, iA) for c, s in fixed(W, VH, m, iA) if s == Wi]
        return PC[k]
    def cyc(f, w):                     # w = u c u^-1, c cyclically reduced
        il = INV[f]; w = list(w); u = []
        while len(w) >= 2 and w[0] == il[w[-1]]:
            u.append(w[0]); w = w[1:-1]
        return tuple(u), tuple(w)
    def root(f, c):                    # c = rho^e, rho = p^j of even length (p string-primitive)
        N = len(c); p = next(c[:d] for d in range(1, N + 1) if N % d == 0 and c == c[:d] * (N // d))
        j = 1 if len(p) % 2 == 0 else 2
        return p * j, N // (len(p) * j)
    def kb_pairs(f, SBmax):            # all B (|B| <= SBmax) inverted by some pure A of family f, |A| <= L (kbottle.py)
        if f == 'h': T, al, ilA, nb, ilB = SQ, m, iA, n, iB       # T[(a, b)] = (b', a'):  a b = b' a'
        else:
            T = VH                                                 # T[(v, h)] = (h', v'):  v h = h' v'
            al, ilA, nb, ilB = n, iB, m, iA
        TI = {v: k for k, v in T.items()}
        def push(S, x):
            S = list(S)
            for i in range(len(S) - 1, -1, -1):
                x, S[i] = T[(S[i], x)]
            return x, tuple(S)
        def back(Tw, y2):
            Tp = []; z = y2
            for t in Tw:
                a, z = TI[(z, t)]; Tp.append(a)
            return tuple(Tp), z
        out = set()
        for p in range(2, L + 1, 2):
            o = [()]
            for _ in range(p): o = [w + (c,) for w in o for c in range(al) if not w or w[-1] != ilA[c]]
            par = {}; lvl = []
            for Aw in o:
                s = (Aw, Aw, -1, -1); par[s] = None; lvl.append(s)
            for d in range(SBmax // 2):
                nxt = []
                for s in lvl:
                    Sw, Tw, lx, ly = s
                    for x in range(nb):
                        if lx >= 0 and x == ilB[lx]: continue
                        x2, S2 = push(Sw, x); T2_, y = back(Tw, ilB[x])
                        if x2 != ilB[y] or (ly >= 0 and y == ilB[ly]): continue
                        t = (S2, T2_, x, y)
                        if S2 == T2_ and x != ilB[y]:
                            fr = [x]; bk = [y]; u = s
                            while par[u] is not None:
                                fr.append(u[2]); bk.append(u[3]); u = par[u]
                            out.add(tuple(reversed(fr)) + tuple(bk))
                        if t not in par and len(par) < 400000: par[t] = s; nxt.append(t)
                lvl = nxt
        return out
    nodes = {}; frames = []; adj = []  # adj[i] = list of (j, kind, rootelement or None)
    def add(g, fr):
        k = key(g)
        if k in nodes: return nodes[k], False
        if len(g[0]) + len(g[1]) > NB: return -1, False
        if len(frames) >= cap: return None, False
        nodes[k] = len(frames); frames.append((g, fr)); adj.append([]); return nodes[k], True
    dq = deque()
    other = {'h': 'v', 'v': 'h'}
    for f in 'hv':
        il = INV[f]; al = m if f == 'h' else n; o = [()]
        for ln in range(1, S + 1):
            o = [w + (c,) for w in o for c in range(al) if not w or w[-1] != il[c]]
            if ln % 2: continue
            for w in o:
                if w[0] == il[w[-1]]: continue
                if not any(pinv(f, w[i:] + w[:i]) for i in range(len(w))): continue
                i, new = add(el(f, w), (((), ()), f, w))
                if new: dq.append(i)
    if SB:                             # extra seeds: every pure pair with |A| <= L and |B| <= SB (flat Klein bottles)
        for f in 'hv':                 # f = family of the inverter A; B is a word of the other family
            fB = other[f]
            for B in kb_pairs(f, SB):
                u, W = cyc(fB, B)
                i, new = add(el(fB, W), (((), ()), fB, W))
                if new: dq.append(i)
    seeds = len(frames); capped = False
    while dq:
        i = dq.popleft(); g, (c, f, W) = frames[i]; il = INV[f]; f2 = other[f]; il2 = INV[f2]
        ci_ = inv(c)
        for t in range(len(W)):
            p = W[:t]; R = W[t:] + W[:t]
            for Aw in pinv(f, R):
                cp = mul(c, el(f, p))
                y0 = mul(mul(cp, el(f2, Aw)), inv(cp))
                u, A2 = cyc(f2, Aw)
                for jj in ((0, 1, -1) if SHIFT else (0,)):
                    # y_j = (c W^j p) A (c W^j p)^-1 = x^2j y_0 also inverts x
                    cj = mul(mul(c, el(f, W if jj > 0 else winv(W, il) if jj < 0 else ())), el(f, p))
                    y = y0 if jj == 0 else mul(mul(cj, el(f2, Aw)), inv(cj))
                    cy = mul(cj, el(f2, u))
                    j, new = add(y, (cy, f2, A2))
                    if j is None: capped = True; continue
                    if j < 0: continue
                    adj[i].append((j, 'K', None))
                    if new: dq.append(j)
        rho, e = root(f, W)
        for fe in (e + 1, e + 2):
            y = mul(mul(c, el(f, red(rho * fe, il))), ci_)
            j, new = add(y, (c, f, red(rho * fe, il)))
            if j is None: capped = True; continue
            if j < 0: continue
            adj[i].append((j, 'P', mul(mul(c, el(f, rho)), ci_) if e > 1 else None))
            if new: dq.append(j)
    return nodes, frames, adj, seeds, capped
def scc(N, adj):                       # iterative Tarjan; returns component id per node
    idx = [-1] * N; low = [0] * N; on = [False] * N; comp = [-1] * N; st = []; cnt = 0; nc = 0
    for s in range(N):
        if idx[s] >= 0: continue
        work = [(s, 0)]; idx[s] = low[s] = cnt; cnt += 1; st.append(s); on[s] = True
        while work:
            v, k = work[-1]
            if k < len(adj[v]):
                work[-1] = (v, k + 1); w = adj[v][k][0]
                if idx[w] < 0:
                    idx[w] = low[w] = cnt; cnt += 1; st.append(w); on[w] = True; work.append((w, 0))
                elif on[w]: low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == idx[v]:
                    while True:
                        w = st.pop(); on[w] = False; comp[w] = nc
                        if w == v: break
                    nc += 1
    return comp
def certificate(frames, adj):
    N = len(frames); comp = scc(N, adj)
    for a in range(N):
        for b, kind, _ in adj[a]:
            if kind == 'K' and comp[a] == comp[b]:
                # shortest path b -> a inside the component, then the K edge a -> b closes the cycle
                par = {b: None}; dq = deque([b])
                while dq and a not in par:
                    u = dq.popleft()
                    for w, k2, r in adj[u]:
                        if comp[w] == comp[a] and w not in par: par[w] = (u, k2, r); dq.append(w)
                path = [a]; steps = []
                while par[path[-1]] is not None:
                    u, k2, r = par[path[-1]]; steps.append((k2, r)); path.append(u)
                path.reverse(); steps.reverse()          # path: b ... a
                chain = [fmt(frames[x][0]) for x in path]
                roots = {str(i): fmt(r) for i, (k2, r) in enumerate(steps) if r is not None}
                return {'chain': chain, 'roots': roots} if roots else chain
    return None
certs = {}
if OUT:
    try: certs = json.load(open(OUT))
    except Exception: certs = {}
for ci in todo:
    for cap in sorted(set([min(CAP, 2000), min(CAP, 12000), CAP])):
        nodes, frames, adj, seeds, capped = run(ci, cap)
        cert = certificate(frames, adj)
        if cert or not capped: break
    rec = {'class': ci, 'L': L, 'S': S, 'NB': NB, 'SB': SB, 'shift': SHIFT, 'seeds': seeds, 'nodes': len(frames),
           'edges': sum(len(x) for x in adj), 'capped': capped, 'cert': cert}
    print(json.dumps(rec), flush=True)
    if LOG: LOG.write(json.dumps(rec) + '\n'); LOG.flush()
    if cert and OUT:
        certs[str(ci)] = cert
        json.dump(certs, open(OUT, 'w'), indent=0)
