# Random one-vertex complete VH complexes beyond the census degrees, run through the solver-free
# pipeline: confluence, reducibility certificate (both automaton images finite, cap 4000), Klein-pair
# count, radius-4 cone-tree search (ctree, C++ port of dtree2.py), independent tree check, and for
# candidates without an R4 tree a radius-6 short-4 cone tree, and failing that cone lemmas (cone.py:
# solver-proposed lemmas, each re-checked by our own unit propagation; no claim rests on a solver answer).
# usage: sample.py m pA n pB seed count out.jsonl      (each sample is one line of out.jsonl)
import sys, json, random, subprocess, os, time
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import VH, finite_image, ball
from vh_enum import inv_arr, orbit
here = os.path.dirname(os.path.abspath(__file__)); CT = os.path.join(here, 'ctree')
TMP = os.environ.get('TMPD', '/tmp')

def random_data(m, pA, n, pB, rng, budget=200000):
    iA = inv_arr(m, pA); iB = inv_arr(n, pB)
    corners = [(h, v) for h in range(m) for v in range(n)]
    targets = [(v, h) for v in range(n) for h in range(m)]
    SQ = {}; img = set(); cnt = [0]
    def rec():
        cnt[0] += 1
        if cnt[0] > budget: return False
        c = next((x for x in corners if x not in SQ), None)
        if c is None: return True
        h, v = c; ts = targets[:]; rng.shuffle(ts)
        for (v2, h2) in ts:
            if (v2, h2) in img: continue
            new = {}; ok = True
            for a, b in orbit(iA, iB, h, v, v2, h2):
                if SQ.get(a, b) != b or new.get(a, b) != b: ok = False; break
                if a not in SQ: new[a] = b
            if not ok: continue
            vals = list(new.values())
            if len(set(vals)) != len(vals) or any(b in img for b in vals): continue
            for a, b in new.items(): SQ[a] = b; img.add(b)
            if rec(): return True
            for a, b in new.items(): del SQ[a]; img.discard(b)
        return False
    return (iA, iB, dict(SQ)) if rec() else None

def cinput(G):
    t = '%d %d\n%s\n%s\n' % (G.m, G.n, ' '.join(map(str, G.iA)), ' '.join(map(str, G.iB)))
    return t + ''.join('%d %d %d %d\n' % (h, v, a, b) for (h, v), (a, b) in sorted(G.SQ.items()))

def parse(G, w):
    """word 'v0h2..' -> normal form via the rewriting system (not the fast multiplication)"""
    out = []; i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j].isdigit(): j += 1
        out.append(('h' if w[i] == 'h' else 'v', int(w[i + 1:j]))); i = j
    return G.rw(out)

def check_tree(G, t):
    """soundness check of a cone tree (format of dtree2.py / ctree): see README"""
    def ev(g):
        v = sum(1 for c in g if c[0] == 'v'); h = len(g) - v
        return len(g) > 0 and v % 2 == 0 and h % 2 == 0
    def inv(g): return G.rw([(c[0], (G.iA if c[0] == 'h' else G.iB)[c[1]]) for c in reversed(g)])
    def go(t, A):
        if t[0] == 'split':
            g = parse(G, t[1])
            if not ev(g): return False
            return go(t[2], A | {g}) and go(t[3], A | {inv(g)})
        (x, y), steps = t[1], t[2]; Q = set(A)
        for z, u, w in steps:
            z, u, w = parse(G, z), parse(G, u), parse(G, w)
            if u not in Q or w not in Q or G.rw(list(u) + list(w)) != z or not ev(z): return False
            Q.add(z)
        x, y = parse(G, x), parse(G, y)
        return x in Q and y in Q and G.rw(list(x) + list(y)) == ()
    return go(t, frozenset())

def klein_pairs(G, R=4):
    """pairs (a, b), b a two-letter kernel element, a in Gamma^+ of length <= R, a b a^-1 = b^-1"""
    idx, els = ball(G, R)
    K = [e for e in els[1:] if len(e[0]) % 2 == 0 and len(e[1]) % 2 == 0]
    def inv(g): return G.mul(((), tuple(G.iA[x] for x in reversed(g[1]))), (tuple(G.iB[x] for x in reversed(g[0])), ()))
    B = [e for e in K if len(e[0]) + len(e[1]) == 2]; n = 0; ex = None
    for b in B:
        bi = inv(b)
        for a in K:
            if G.mul(G.mul(a, b), inv(a)) == bi:
                n += 1; ex = ex or [a, b]
    return n, ex

def ctree(G, R, sh, maxl, tmo, cnf=None):
    env = dict(os.environ); env.pop('CNF', None)
    if cnf: env['CNF'] = cnf
    p = subprocess.run([CT, str(R), str(sh), str(maxl), str(tmo), '0'], input=cinput(G), capture_output=True,
                       text=True, env=env, timeout=tmo + 600)
    return p.returncode, p.stdout, p.stderr

def cnf_sat(G, R, sh):
    from pysat.formula import CNF
    from pysat.solvers import Cadical153
    f = os.path.join(TMP, 'w13s_%d.cnf' % os.getpid())
    ctree(G, R, sh, 0, 0, cnf=f)
    F = CNF(from_file=f); nv, nc = F.nv, len(F.clauses)
    with Cadical153(bootstrap_with=F.clauses) as s: r = s.solve()
    for e in ('', '.map'):
        if os.path.exists(f + e): os.unlink(f + e)
    return [r, nv, nc]

if __name__ == '__main__':
    m, pA, n, pB, seed, count = map(int, sys.argv[1:7]); out = sys.argv[7]
    rng = random.Random(seed); k = 0
    while k < count:
        d = random_data(m, pA, n, pB, rng)
        if d is None: continue
        t0 = time.time(); iA, iB, SQ = d; G = VH(iA, iB, SQ); G.confluence()
        rec = dict(pat='%d%d_%d%d' % (m, pA, n, pB), seed=seed, k=k, sq=sorted([list(a), list(b)] for a, b in SQ.items()))
        rec['finH'] = finite_image(G, True); rec['finV'] = finite_image(G, False)
        rec['cand'] = rec['finH'] is None or rec['finV'] is None
        if rec['cand']:
            rec['klein'] = klein_pairs(G)[0]
            c, o, e = ctree(G, 4, -1, 4000, 300)
            if c == 0:
                t = json.loads(o); rec['tree4'] = [t['depth'], t['leaves'], check_tree(G, t['tree'])]
                os.makedirs(os.path.join(here, 'trees'), exist_ok=True)
                json.dump(t, open(os.path.join(here, 'trees', '%s_s%d_k%d_R4.json' % (rec['pat'], seed, k)), 'w'))
            else:
                rec['tree4'] = None
                c, o, e = ctree(G, 6, 4, 300000, 450)
                if c == 0:
                    t = json.loads(o); rec['tree6s4'] = [t['depth'], t['leaves'], check_tree(G, t['tree'])]
                    os.makedirs(os.path.join(here, 'trees'), exist_ok=True)
                    json.dump(t, open(os.path.join(here, 'trees', '%s_s%d_k%d_R6s4.json' % (rec['pat'], seed, k)), 'w'))
                else:
                    rec['tree6s4'] = None; import cone; rec['cone6s4'] = cone.run(rec, 6, 4)
        rec['sec'] = round(time.time() - t0, 1)
        open(out, 'a').write(json.dumps(rec) + '\n'); k += 1
