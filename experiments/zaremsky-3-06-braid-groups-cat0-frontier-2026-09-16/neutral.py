import sys, runpy
# reuse the definitions of nc_pairs.py without running its main search
src = open('nc_pairs.py').read().split('# ---------- main search ----------')[0]
g = {'__name__': 'lib'}
sys.argv = ['nc_pairs.py', sys.argv[1]]
exec(compile(src, 'nc_pairs_lib', 'exec'), g)
N, NC, leq, fail_mod, universal, ZERO, ONE, show, rank = g['N'], g['NC'], g['leq'], g['fail_mod'], g['universal'], g['ZERO'], g['ONE'], g['show'], g['rank']
neutral = []
for i in range(N):
    if i in (ZERO, ONE): continue
    if all(leq[i, j] or leq[j, i] or not fail_mod(i, j) for j in range(N)):
        neutral.append(i)
print("n =", g['n'], "neutral vertices:", len(neutral), "universal vertices:", sum(universal[i] for i in range(N) if i not in (ZERO, ONE)))
print("neutral but not universal:", [show(i) for i in neutral if not universal[i]][:20])
print("universal but not neutral:", [show(i) for i in range(N) if universal[i] and i not in (ZERO, ONE) and i not in neutral][:20])
