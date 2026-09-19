"""Meet-in-the-middle search for generalized torsion of y in G(K; al, be):
products y_0 * c_2 * ... * c_m = 1 with each c_j = u^-1 y_i u a conjugate of y (u a word of length <= ell in
y_j, j in a window). Candidates are matched by their images in finite permutation quotients (perms.txt from
lowindex.g), then every candidate is decided exactly with tower_wp.
usage: gt_search.py K al be permsfile m ell window
"""
import sys, itertools
from tower_wp import Tower, inv

K, al, be = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
permsfile, m, ell, win = sys.argv[4], int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])

reps = []
for line in open(permsfile):
    parts = line.split(' ', 1)
    rest = parts[1].strip().rsplit(' ', 1)[0]
    a, b = rest.split('] [')
    Y = tuple(int(x) - 1 for x in a.strip('[] ').split(','))
    Tt = tuple(int(x) - 1 for x in b.strip('[] ').split(','))
    reps.append((Y, Tt))
reps.sort(key=lambda r: -len(r[0]))
reps = reps[:24]

def mul(p, q):  # apply p then q (right action, matching GAP)
    return tuple(q[p[i]] for i in range(len(p)))

def pinv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)

def ppow(p, k):
    n = len(p)
    r = tuple(range(n))
    base = p if k >= 0 else pinv(p)
    for _ in range(abs(k)):
        r = mul(r, base)
    return r

idx = range(-win, win + 1)
# images of y_i = t^-i y t^i
Yimg = {}
for i in range(-win - 1, win + 2):
    Yimg[i] = [mul(mul(ppow(T, -i), Y), ppow(T, i)) for (Y, T) in reps]
ident = [tuple(range(len(Y))) for (Y, T) in reps]

def img(w):
    r = ident
    for (i, e) in w:
        g = Yimg[i] if e == 1 else [pinv(p) for p in Yimg[i]]
        r = [mul(x, y) for x, y in zip(r, g)]
    return tuple(r)

letters = [(i, e) for i in idx for e in (1, -1)]
words = [()]
for L in range(1, ell + 1):
    for w in itertools.product(letters, repeat=L):
        if all(not (w[j][0] == w[j + 1][0] and w[j][1] == -w[j + 1][1]) for j in range(L - 1)):
            words.append(tuple(w))
conj = {}
for i in idx:
    for u in words:
        c = inv(u) + ((i, 1),) + u
        if u and u[0][0] == i:
            continue  # conjugating y_i by y_i^{+-1}... is redundant
        conj[(i, u)] = (img(c), (i, c))
conjs = list(conj.values())
print('conjugates:', len(conjs), flush=True)

def mulimg(a, b):
    return tuple(mul(x, y) for x, y in zip(a, b))

T = Tower(K, al, be)
y0 = img(((0, 1),))
ml = m // 2
left = {}
for combo in itertools.product(range(len(conjs)), repeat=ml - 1):
    h = y0
    for j in combo:
        h = mulimg(h, conjs[j][0])
    left.setdefault(h, []).append(combo)
print('left products:', len(left), flush=True)
found, checked = [], 0
for combo in itertools.product(range(len(conjs)), repeat=m - ml):
    cnt = {}
    h = ident_t = tuple(ident)
    for j in combo:
        h = mulimg(h, conjs[j][0])
    target = tuple(pinv(p) for p in h)
    if target in left:
        for lc in left[target]:
            w = ((0, 1),)
            idxs = [0]
            for j in lc + combo:
                w = w + conjs[j][1][1]
                idxs.append(conjs[j][1][0])
            if any(idxs.count(i) % 2 for i in set(idxs)):
                continue
            checked += 1
            if T.trivial_N(w):
                found.append(w)
                print('FOUND', w, flush=True)
print('m', m, 'ell', ell, 'win', win, 'exact checks', checked, 'found', len(found))
