# Disc invariant relative to the fixed arc x_0 (w18-042): per outside puncture j the three coordinates
# e_{F_a j} - e_{m j} (a = 0,1,2).  B°-meridians have e_{mj} = 0 and point-pushing along F changes no
# outside coordinate, so every disc of the Helly problem has iota in Lambda_full = span(meridian vectors).
import sys; sys.path.insert(0, sys.path[0])
src = open(sys.path[0] + '/lattice.py').read().split('# ---- gluing')[0]
exec(src.replace("print(' ', t[0]", "pass  # print(' ', t[0]"))
import flint, itertools
J = len(out); rows3 = []
for k, pairs in planes.items():
    v = [0] * (3 * J)
    for C in clusters(pairs):
        for a in range(3):
            if Fi[a] in C:
                for j in C:
                    if j in col: v[3 * col[j] + a] += 1
    rows3.append(v)
rows3.append([-1] * (3 * J))   # m circling all punctures along a section loop (allowed, only enlarges Lambda)
L3 = Matrix(rows3)
print('rank Lambda_full in Z^%d:' % (3 * J), L3.rank())
print('mixed-F meridian vectors:', sum(1 for v in rows3 if len({c % 3 for c, x in enumerate(v) if x}) > 1))
def proj(S):   # coordinates of the F-indices in S (the F-punctures of one pair hull, together with m)
    return Matrix([[1 if c == 3 * t + a else 0 for c in range(3 * J)] for t in range(J) for a in S])
def glue_rank(pattern):
    cons = []
    for S in pattern:
        Pm = proj(S); ann = (Pm * L3.T).T.nullspace(); cons += [a.T * Pm for a in ann]
    Cm = Matrix.vstack(*cons) if cons else Matrix.zeros(0, 3 * J)
    return 3 * J - Cm.rank()
for pattern in ([(0, 2), (1, 2), (0, 1)], [(0,), (1,), (2,)], [(0, 1), (2,)], [(0, 1, 2)]):
    print('pair-hull F-sets', pattern, ': gluing closure rank', glue_rank(pattern), 'vs', L3.rank())

# ---- all hull patterns allowed by homology ----
# S12, S13, S23 = F-sets of the three pair hulls (nonempty).  Classes c2=[t2], c3=[t3]: supp c2 in S12,
# supp c3 in S13, supp(c3-c2) in S23; a one-puncture hull carries a nonzero power of a simple loop.
snf3 = smith_normal_form(L3.T); print('Lambda_full saturated:', all(abs(snf3[i, i]) in (0, 1) for i in range(min(snf3.shape))))
subsets = [S for r in (1, 2, 3) for S in itertools.combinations(range(3), r)]
def feasible(S12, S13, S23):
    rngv = range(-1, 2)
    for c2 in itertools.product(rngv, repeat=3):
        for c3 in itertools.product(rngv, repeat=3):
            d = tuple(y - x for x, y in zip(c2, c3)); ok = True
            for S, c in ((S12, c2), (S13, c3), (S23, d)):
                if any(c[a] for a in range(3) if a not in S): ok = False
                if len(S) == 1 and c[S[0]] == 0: ok = False
            if ok: return True
    return False
res = {}
for S12 in subsets:
    for S13 in subsets:
        for S23 in subsets:
            if not feasible(S12, S13, S23): continue
            U = tuple(sorted(set(S12) | set(S13) | set(S23)))
            key = (U, tuple(sorted({S12, S13, S23})))
            if key in res: continue
            PU = proj(U); base = (PU * L3.T).rank()
            # gluing closure inside the coordinates U (missing F-punctures are attached freely)
            cons = []
            for S in (S12, S13, S23):
                Pm = proj(S); ann = (Pm * L3.T).T.nullspace(); cons += [a.T * Pm for a in ann]
            Cm = Matrix.vstack(*cons) if cons else Matrix.zeros(0, 3 * J)
            # restrict to coordinates U: closure rank = dim{z_U : constraints} ; constraints only touch U
            g = len(U) * J - (Cm * PU.T).rank() if cons else len(U) * J
            res[key] = (g, base)
for key, (g, base) in sorted(res.items()):
    print('hull F-set', key[0], 'pair-hull F-sets', key[1], ': closure', g, 'orbit', base, 'GAP' if g > base else 'ok', '| every F-pair in a common pair hull:', all(any({a, b} <= set(S) for S in key[1]) for a, b in itertools.combinations(key[0], 2)))
