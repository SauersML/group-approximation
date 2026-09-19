"""Shortest VC failures in type A_4, computed only with the faithful Artin representation (independent of cchelly).
Uses lemma (Q): for k != 1 with U_a(k) = w C_N(a), U_b(k) = w C_N(b), VC fails for (u, v) = (wc, wd) iff
c in C_N(a) \ C_N(b) and d in C_N(b) \ C_N(a).  So a VC failure is a triple of witnesses:
  w in N with [w,a] = [w,b] != 1,  c in C_N(a) \ C_N(b),  d in C_N(b) \ C_N(a).
For F-words a != b of length <= LA and N-words of length <= LB it finds the shortest such witnesses, then checks the
resulting (u, v) = (wc, wd) directly: [u,a] = [v,b] = k != 1, [u,b] != k, [v,a] != k.
usage: python3 a4vcmin.py LA LB"""
import sys, itertools
sys.argv = [sys.argv[0], 'A4', '/dev/null'] + sys.argv[1:]
exec(open('artinverify.py').read().split('ID = rep([])')[0])
LA, LB = int(sys.argv[3]), int(sys.argv[4])
def ap(f, x):  # apply automorphism f (tuple of images of t_1..t_m) to a word x
    return red([h for t in x for h in (f[t - 1] if t > 0 else [-g for g in reversed(f[-t - 1])])])
def cmp(f, g): return tuple(tuple(ap(f, g[j])) for j in range(m))  # f o g
def ball(pre, R):
    gens = [k for k in L if k.startswith(pre)]
    A = {(): rep([])}; fr = [()]
    for _ in range(R):
        nf = []
        for t in fr:
            for g in gens:
                if t and (t[-1] == g + "'" or g == t[-1] + "'"): continue
                A[t + (g,)] = cmp(A[t], rep(L[g])); nf.append(t + (g,))
        fr = nf
    return A
FA, NA = ball('p', LA), ball('x', LB)
INV = lambda t: tuple((g[:-1] if g.endswith("'") else g + "'") for g in reversed(t))
def aut(t): return FA[t] if t in FA else NA[t]
def com(x, y): return cmp(cmp(aut(x), aut(y)), cmp(aut(INV(x)), aut(INV(y))))
ID = rep([])
FB = [t for t in FA if t]; NB = sorted(NA, key=len)
Cen = {a: [c for c in NB if cmp(aut(c), aut(a)) == cmp(aut(a), aut(c))] for a in FB}
Com = {a: {c: com(c, a) for c in NB} for a in FB}
best = []
for a, b in itertools.combinations(FB, 2):
    Ca, Cb = set(Cen[a]), set(Cen[b])
    c = [x for x in Cen[a] if x not in Cb]; d = [x for x in Cen[b] if x not in Ca]
    ws = [x for x in NB if Com[a][x] == Com[b][x] and Com[a][x] != ID]
    if c and d and ws:
        best.append((len(a) + len(b) + len(ws[0]) + len(c[0]) + len(d[0]), a, b, ws[0], c[0], d[0]))
best.sort()
print(f'LA={LA} LB={LB} |FB|={len(FB)} |NB|={len(NB)} pairs with VC failures: {len(best)}')
def M(t): return [g for tok in t for g in L[tok]]
for tot, a, b, w_, c, d in best[:8]:
    u, v = w_ + c, w_ + d
    k = rep(comm(M(u), M(a)))
    ok = k == rep(comm(M(v), M(b))) and k != ID and rep(comm(M(u), M(b))) != k and rep(comm(M(v), M(a))) != k
    print(tot, 'a=', ' '.join(a), '| b=', ' '.join(b), '| w=', ' '.join(w_), '| c=', ' '.join(c), '| d=', ' '.join(d),
          '| VC failure at (u,v)=(wc,wd) confirmed:', ok)
