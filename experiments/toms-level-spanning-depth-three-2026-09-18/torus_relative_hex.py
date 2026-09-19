"""Relative Hex on a punctured torus (or a disk), triangular lattice, 6-adjacency for both colours.
H components must miss one of L,R and one of T,B; complement components must miss a side.
Score = number of bad components; 0 = counterexample to the relative Hex statement.
usage: python3 torus_relative_hex.py n k steps seed [disk]"""
import sys, random, math
n, k, steps, seed = map(int, sys.argv[1:5]); disk = len(sys.argv) > 5
rng = random.Random(seed)
D = [(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
def wrap(i, j):
    if disk:
        return (i, j) if 0 <= i < n and 0 <= j < n else None
    return (i % n, j % n)
off = (n - k) // 2
hole = {(off + a, off + b) for a in range(k) for b in range(k)}
cells = [(i, j) for i in range(n) for j in range(n) if (i, j) not in hole]
idx = {c: t for t, c in enumerate(cells)}
nb = []
for (i, j) in cells:
    l = []
    for di, dj in D:
        w = wrap(i + di, j + dj)
        if w is not None and w in idx: l.append(idx[w])
    nb.append(l)
side = [0] * len(cells)   # bitmask L=1,R=2,B=4,T=8
plain = (k == 0)
for t, (i, j) in enumerate(cells):
    if plain:
        side[t] = (i == 0) * 1 | (i == n - 1) * 2 | (j == 0) * 4 | (j == n - 1) * 8
        continue
    for di, dj in D:
        if wrap(i + di, j + dj) in hole:
            if i < off: side[t] |= 1
            if i >= off + k: side[t] |= 2
            if j < off: side[t] |= 4
            if j >= off + k: side[t] |= 8
# conservative corners: consecutive boundary cells with different labels share their labels
# exact semantics: the midpoint between consecutive boundary cells of different colours lies in H,
# so an H cell also meets its boundary neighbours' sides; complement cells keep their own labels.
orig = side[:]
sideH = side[:]
for t in range(len(cells)):
    if orig[t]:
        for v in nb[t]:
            if orig[v]: sideH[t] |= orig[v]
def score(col):
    seen = [False] * len(cells); bad = 0
    for s in range(len(cells)):
        if seen[s]: continue
        c = col[s]; st = [s]; seen[s] = True; m = 0
        while st:
            u = st.pop(); m |= (sideH[u] if c else orig[u])
            for v in nb[u]:
                if not seen[v] and col[v] == c: seen[v] = True; st.append(v)
        if c: bad += ((m & 3) == 3) or ((m & 12) == 12)
        else: bad += (m == 15)
    return bad
col = [rng.random() < 0.4 for _ in cells]
cur = score(col); best = cur; T0 = 1.0
for it in range(steps):
    T = T0 * (1 - it / steps) + 0.02
    u = rng.randrange(len(cells)); col[u] = not col[u]
    s = score(col)
    if s <= cur or rng.random() < math.exp((cur - s) / T): cur = s
    else: col[u] = not col[u]
    if cur < best: best = cur
    if cur == 0: break
print("n", n, "k", k, "disk", disk, "best", best, "cur", cur)
print("labels", sorted(set(side)))
if cur == 0:
    for j in reversed(range(n)):
        print(" " * (n - j) + " ".join("#" if (i, j) in hole else ("H" if col[idx[(i, j)]] else ".") for i in range(n)))
