"""Union of B-orbits of random vertices of T_B at distance L from v, as GAP permutations of b, d.
usage: python3 orbits.py e L N seed cap  -> writes orb_e<e>_L<L>.g ; prints the degree."""
import sys, random
from mult import make
e, L, N, seed = map(int, sys.argv[1:5]); cap = int(sys.argv[5]) if len(sys.argv) > 5 else 3000000
m, T, bu, du, a = make(e)
random.seed(seed)
idx = {}; pts = []
def add(x):
    if x not in idx: idx[x] = len(pts); pts.append(x); return True
    return False
for _ in range(N):
    x = tuple([random.randrange(m)] + [random.randrange(1, m) for _ in range(L - 1)])
    if x in idx: continue
    add(x); q = [x]
    while q:
        y = q.pop()
        for z in (bu(1, y), du(1, y)):
            if add(z): q.append(z)
    if len(pts) > cap: break
pb = [idx[bu(1, x)] + 1 for x in pts]; pd = [idx[du(1, x)] + 1 for x in pts]
with open('orb_e%d_L%d.g' % (e, L), 'w') as f:
    f.write('pb:=PermList(%s);;\npd:=PermList(%s);;\n' % (pb, pd))
print(e, L, len(pts))
