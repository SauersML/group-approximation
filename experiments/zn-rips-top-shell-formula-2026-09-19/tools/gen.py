# gen.py n r order: writes L-n-r.txt (Lmax_n) and K-n-r-<order>.txt: K u | e_j+e_n for all u with |u|=r, u_n=0, u>0
# order: 'desc' = by j descending, 'asc' = by j ascending (then lexicographic)
import sys, itertools
n, r, order = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
def pts(n, rem):
    if n == 0: yield (); return
    for v in range(-rem, rem + 1):
        for t in pts(n - 1, rem - abs(v)): yield (v,) + t
L = [p for p in pts(n, r) if any(p) and [c for c in p if c][-1] > 0]
with open(f'L-{n}-{r}.txt', 'w') as f:
    for p in L: f.write(' '.join(map(str, p)) + '\n')
U = [p for p in L if sum(map(abs, p)) == r and p[-1] == 0]
def j(p): return max(i for i in range(n) if p[i])
U.sort(key=lambda p: (-j(p) if order == 'desc' else j(p), p))
with open(f'K-{n}-{r}-{order}.txt', 'w') as f:
    for p in U:
        w = [0] * n; w[j(p)] = 1; w[-1] = 1
        f.write('K ' + ' '.join(map(str, p)) + ' | ' + ' '.join(map(str, w)) + '\n')
print(n, r, len(L), len(U))
