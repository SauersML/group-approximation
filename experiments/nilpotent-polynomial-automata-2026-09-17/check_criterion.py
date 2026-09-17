"""Falsification check for nilpotent-polynomial-automata-reduce-to-kaplansky.

Over a finite host G = Z/n (where group algebras are directly finite), the theorem predicts:
for a finite nilpotent alphabet group Q and a Q-polynomial automaton
    tau(x)_g = w(x_{g+m_1}, ..., x_{g+m_k})     (w a word in variables and constants of Q),
tau is bijective  <=>  alpha = sum_j e_j [m_j] is a unit of (Z/e_ab)[Z/n],
where e_j is the exponent sum of variable j in w and e_ab = exponent of Q^ab.
For non-nilpotent Q (S_3) the criterion is expected to fail somewhere.
Brute force over all configurations. Single-threaded, small.
"""
import itertools, random, sys
from math import gcd

def perm_group(gens, n):
    idt = tuple(range(n))
    els = {idt}; frontier = [idt]
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                b = tuple(g[a[i]] for i in range(n))
                if b not in els:
                    els.add(b); new.append(b)
        frontier = new
    els = sorted(els)
    idx = {e: i for i, e in enumerate(els)}
    mul = [[idx[tuple(b[a[i]] for i in range(n))] for b in els] for a in els]  # a then b
    e = idx[idt]
    inv = [next(j for j in range(len(els)) if mul[i][j] == e) for i in range(len(els))]
    return mul, inv, e

def cyc(n):  # Z/n
    return perm_group([tuple((i + 1) % n for i in range(n))], n)

def product(G1, G2):
    m1, i1, e1 = G1; m2, i2, e2 = G2
    a, b = len(m1), len(m2)
    mul = [[m1[x // b][y // b] * b + m2[x % b][y % b] for y in range(a * b)] for x in range(a * b)]
    inv = [i1[x // b] * b + i2[x % b] for x in range(a * b)]
    return mul, inv, e1 * b + e2

def table_group(elements, op):
    idx = {x: i for i, x in enumerate(elements)}
    mul = [[idx[op(a, b)] for b in elements] for a in elements]
    N = len(elements)
    e = next(i for i in range(N) if all(mul[i][j] == j for j in range(N)))
    inv = [next(j for j in range(N) if mul[i][j] == e) for i in range(N)]
    return mul, inv, e

def quaternion():
    # elements (s, u) with s in {+1,-1}, u in {1,i,j,k}
    tab = {('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
           ('i','1'):(1,'i'),('i','i'):(-1,'1'),('i','j'):(1,'k'),('i','k'):(-1,'j'),
           ('j','1'):(1,'j'),('j','i'):(-1,'k'),('j','j'):(-1,'1'),('j','k'):(1,'i'),
           ('k','1'):(1,'k'),('k','i'):(1,'j'),('k','j'):(-1,'i'),('k','k'):(-1,'1')}
    els = [(s, u) for s in (1, -1) for u in '1ijk']
    def op(a, b):
        s, u = tab[(a[1], b[1])]
        return (a[0] * b[0] * s, u)
    return table_group(els, op)

def heisenberg(p):
    els = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]
    return table_group(els, lambda x, y: ((x[0]+y[0]) % p, (x[1]+y[1]) % p, (x[2]+y[2]+x[0]*y[1]) % p))

GROUPS = {
    'Z4': cyc(4),
    'Z2xZ2': product(cyc(2), cyc(2)),
    'D4': perm_group([(1, 2, 3, 0), (0, 3, 2, 1)], 4),
    'Q8': quaternion(),
    'Heis3': heisenberg(3),
    'A4': perm_group([(1, 2, 0, 3), (1, 0, 3, 2)], 4),
    'S3': perm_group([(1, 0, 2), (1, 2, 0)], 3),
    'Z6': cyc(6),
}

def order_info(G):
    mul, inv, e = G
    N = len(mul)
    # commutator subgroup
    comms = {mul[mul[inv[a]][inv[b]]][mul[a][b]] for a in range(N) for b in range(N)}
    H = set(comms) | {e}
    changed = True
    while changed:
        changed = False
        for a in list(H):
            for b in list(H):
                c = mul[a][b]
                if c not in H:
                    H.add(c); changed = True
    # exponent of Q/H: smallest t with g^t in H for all g
    def pw(g, t):
        r = e
        for _ in range(t):
            r = mul[r][g]
        return r
    t = 1
    while not all(pw(g, t) in H for g in range(N)):
        t += 1
    return t

def is_nilpotent(G):
    mul, inv, e = G
    N = len(mul)
    # upper central series
    Z = {e}
    while True:
        newZ = {z for z in range(N) if all(mul[mul[inv[z]][inv[g]]][mul[z][g]] in Z for g in range(N))}
        if newZ == Z:
            return len(Z) == N
        Z = newZ

def random_word(k, N, length):
    # letters: ('x', j, +-1) or ('c', q)
    w = []
    for _ in range(length):
        if random.random() < 0.3:
            w.append(('c', random.randrange(N)))
        else:
            w.append(('x', random.randrange(k), random.choice((1, -1))))
    return w

def eval_word(G, w, vals):
    mul, inv, e = G
    r = e
    for L in w:
        if L[0] == 'c':
            r = mul[r][L[1]]
        else:
            v = vals[L[1]]
            r = mul[r][v if L[2] == 1 else inv[v]]
    return r

def alpha_unit(w, k, mem, n, eab):
    es = [0] * k
    for L in w:
        if L[0] == 'x':
            es[L[1]] += L[2]
    alpha = [0] * n
    for j in range(k):
        alpha[mem[j] % n] = (alpha[mem[j] % n] + es[j]) % eab
    seen = set()
    for v in itertools.product(range(eab), repeat=n):
        img = tuple(sum(v[h] * alpha[(g - h) % n] for h in range(n)) % eab for g in range(n))
        seen.add(img)
    return len(seen) == eab ** n

def tau_bijective(G, w, k, mem, n):
    N = len(G[0])
    imgs = set()
    for x in itertools.product(range(N), repeat=n):
        y = tuple(eval_word(G, w, [x[(g + mem[j]) % n] for j in range(k)]) for g in range(n))
        imgs.add(y)
    return len(imgs) == N ** n

def main():
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    for name, G in GROUPS.items():
        N = len(G[0]); eab = order_info(G); nil = is_nilpotent(G)
        for n in (2, 3, 4):
            if N ** n > 20000:
                continue
            agree = disagree = 0; examples = []
            nb = 0
            for _ in range(trials):
                k = random.choice((2, 3))
                mem = [random.randrange(n) for _ in range(k)]
                w = random_word(k, N, random.randrange(2, 9))
                b = tau_bijective(G, w, k, mem, n)
                u = alpha_unit(w, k, mem, n, eab)
                nb += b
                if b == u:
                    agree += 1
                else:
                    disagree += 1
                    if len(examples) < 2:
                        examples.append((w, mem, b, u))
            print(f"Q={name:6s} |Q|={N} nilpotent={nil} e_ab={eab} n={n}: agree={agree} disagree={disagree} bijective={nb}")
            for ex in examples:
                print("   example", ex)

if __name__ == '__main__':
    main()
