"""Exact Case 1 search in the commutator form of research/h4-case1-helly-is-a-commutator-double-coset-problem.md.

Theorem used (proved there): with a = alpha_1^-1, b = alpha_2, u = beta_3, v = beta_3 beta_1 (all in P, Garside-exact),
  (*)  <=>  [u, a] = [v, b] =: k ,
  pure bound (H)  <=>  [w, a] = [w, b] = k for some w in N ,
  vertex centre (VC) <=>  w in {1, u, v} works  (w = 1 iff k = 1; w = u iff [u, b] = k; w = v iff [v, a] = k).
So for each F-element f we hash u -> [u, f] over a ball of N once (O(|ball|) normal forms), and every Case 1
tuple of the box is a pair (u, v) in one hash class of a and of b.  No shadows, no Burau hashing, no false hits.

N-ball: distinct elements of word length <= LB in the 12 meridian letters x0..x11 of N (dedup by normal form).
F-ball: distinct elements of word length <= LA in p1, p2, p3.
Output per ordered pair (alpha_1, alpha_2) with alpha_1, alpha_2, alpha_1 alpha_2 != 1:
  tuples = genuine Case 1 tuples (u, v) with k != 1 in the box;  VCFAIL = tuples with no vertex centre;
  HBALL  = VCFAIL tuples whose class k still has a common w in the ball (a non-vertex pure centre);
  HCAND  = VCFAIL tuples with no common w in the ball (would need the full double coset test).
Selftest (option 'self'): checks the retraction lemma  beta f beta^-1 in F  =>  beta f beta^-1 = f  on the balls,
with the independent membership test fmem.in_F of experiments/h4-vertex-centre-2026-09-18.
Run: python3 chelly.py LA LB [self]"""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
for p in (os.path.join(HERE, '..', 'h4-artin-complex-6cycles-2026-09-17'),
          '/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17'):
    if os.path.exists(os.path.join(p, 'garside.py')):
        sys.path.insert(0, p)
        break
from garside import Coxeter, Artin

W4 = Coxeter(4, {(0, 1): 3, (1, 2): 3, (2, 3): 5})
G = Artin(W4)
FW = {'p3': [1, 1], 'p2': [1, 2, 2, -1], 'p1': [1, 2, 3, 3, -2, -1]}
NW = {'x0': [4, 4], 'x1': [3, 4, 4, -3], 'x3': [4, 3, 3, -4], 'x2': [3, 4, 3, 3, -4, -3],
      'x4': [2, 3, 4, 4, -3, -2], 'x11': [2, 4, 3, 3, -4, -2], 'x5': [2, 3, 4, 3, 3, -4, -3, -2],
      'x10': [3, 2, 4, 3, 3, -4, -2, -3], 'x6': [2, 3, 2, 4, 3, 3, -4, -2, -3, -2],
      'x9': [4, 3, 2, 4, 3, 3, -4, -2, -3, -4], 'x7': [2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2],
      'x8': [3, 2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2, -3]}


def ball(gens, L):
    """distinct elements of word length <= L: list of (normal form, spelling)"""
    lets = []
    for n, w in gens.items():
        lets.append((n, G.word(w)))
        lets.append((n + "'", G.inv(G.word(w))))
    seen = {G.one: ''}
    front = [G.one]
    for _ in range(L):
        new = []
        for g in front:
            for n, x in lets:
                h = G.mul(g, x)
                if h not in seen:
                    seen[h] = (seen[g] + ' ' + n).strip()
                    new.append(h)
        front = new
    return list(seen.items())


def comm(x, xi, f, fi):
    return G.mul(G.mul(G.mul(x, f), xi), fi)


def main(LA, LB, selftest=False):
    t0 = time.time()
    FB = ball(FW, LA)
    NB = ball(NW, LB)
    NI = [G.inv(g) for g, _ in NB]
    print('F-ball', len(FB), 'N-ball', len(NB), round(time.time() - t0), 's', flush=True)
    idx = {g: i for i, (g, _) in enumerate(FB)}
    key = {}
    for g, s in FB:
        gi = G.inv(g)
        key[g] = [hash(comm(x, NI[j], g, gi)) for j, (x, _) in enumerate(NB)]   # 64-bit hash; hits re-verified exactly
    one = hash(G.one)
    D = {}
    for g, s in FB:
        d = {}
        for j, k in enumerate(key[g]):
            if k != one:
                d.setdefault(k, []).append(j)
        D[g] = d
    print('hashed', round(time.time() - t0), 's', flush=True)
    if selftest:
        import importlib.util
        cands = [os.path.join(HERE, '..', 'h4-vertex-centre-2026-09-18', 'fmem.py'),
                 '/home/user/group-approximation/experiments/h4-vertex-centre-2026-09-18/fmem.py',
                 os.path.join(HERE, '..', '..', '..', 'w12-042', 'experiments', 'h4-vertex-centre-2026-09-18', 'fmem.py')]
        spec = importlib.util.spec_from_file_location('fmem', next(p for p in cands if os.path.exists(p)))
        fm = importlib.util.module_from_spec(spec); spec.loader.exec_module(fm)
        bad = inF = tot = 0
        for g, s in FB[1:8]:
            for j, (x, sx) in enumerate(NB[:400]):
                c = G.mul(G.mul(x, g), NI[j])
                mem = fm.in_Y(c) is not None and fm.G3.word(fm.forget1(fm.in_Y(c))) == fm.G3.one
                tot += 1; inF += mem
                if mem != (c == g):
                    bad += 1; print('SELFTEST FAIL', s, '|', sx, flush=True)
        print('selftest: pairs', tot, 'conjugate in F', inF, 'violations', bad, flush=True)
    st = dict(pairs=0, trivial_k=0, tuples=0, VCFAIL=0, HBALL=0, HCAND=0)
    for g1, s1 in FB[1:]:
        a = G.inv(g1)
        ka, Da = key[a], D[a]
        for g2, s2 in FB[1:]:
            if G.mul(g1, g2) == G.one:
                continue
            kb, Db = key[g2], D[g2]
            st['pairs'] += 1
            st['trivial_k'] += ka.count(one) * kb.count(one)
            for k in Da.keys() & Db.keys():
                U, V = Da[k], Db[k]
                gi2 = G.inv(g2)
                # exact re-verification of (*) in the form [u,a] = [v,b]
                U = [j for j in U if comm(NB[j][0], NI[j], a, g1) == comm(NB[V[0]][0], NI[V[0]], g2, gi2)]
                V = [j for j in V if U and comm(NB[j][0], NI[j], g2, gi2) == comm(NB[U[0]][0], NI[U[0]], a, g1)]
                if not U or not V:
                    st['hash collision'] = st.get('hash collision', 0) + 1
                    continue
                st['tuples'] += len(U) * len(V)
                Ux = [j for j in U if kb[j] != k]      # u fails w = u
                Vx = [j for j in V if ka[j] != k]      # v fails w = v
                n = len(Ux) * len(Vx)
                if not n:
                    continue
                st['VCFAIL'] += n
                common = set(U) & set(V)
                if common:
                    st['HBALL'] += n
                    w = min(common)
                    print('HBALL', s1, '|', s2, '| u', NB[Ux[0]][1], '| v', NB[Vx[0]][1], '| w', NB[w][1], flush=True)
                else:
                    st['HCAND'] += n
                    print('HCAND', s1, '|', s2, '| u', NB[Ux[0]][1], '| v', NB[Vx[0]][1], flush=True)
        if st['pairs'] % 2000 < len(FB):
            print('progress', st, round(time.time() - t0), 's', flush=True)
    print(st, round(time.time() - t0), 's', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), len(sys.argv) > 3)
