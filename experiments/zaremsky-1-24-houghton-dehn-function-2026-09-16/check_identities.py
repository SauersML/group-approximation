"""Exact permutation checks for the H_3 identities used in
notes/zaremsky-1-24-houghton-dehn-function-swarm-2026-09-16.md.
Right actions: word = list of letters applied left to right. Points (ray, depth).
Checks are exact on all points of depth <= D, with D much larger than word lengths."""
D = 60
PTS = [(r, p) for r in (1, 2, 3) for p in range(1, D + 1)]

def lam(a, b):
    def f(x):
        r, p = x
        if r == a:
            return (a, p - 1) if p >= 2 else (b, 1)
        if r == b:
            return (b, p + 1)
        return x
    return f

def inv(f):
    table = {}
    for r in (1, 2, 3):
        for p in range(1, D + 20):
            table[f((r, p))] = (r, p)
    return lambda x: table[x]

def trans(x, y):
    return lambda z: y if z == x else (x if z == y else z)

g1, g2 = lam(1, 2), lam(1, 3)
G = {'g1': g1, 'g2': g2, 'G1': inv(g1), 'G2': inv(g2), 'a': trans((1, 1), (1, 2))}

def word(w):
    fs = [G[s] for s in w]
    def f(x):
        for h in fs:
            x = h(x)
        return x
    return f

def pos(p):  # line Lambda = ray2 u ray1, position 0 = (1,1)
    return (1, p + 1) if p >= 0 else (2, -p)

def eq(f, h, depth=30):
    return all(f(x) == h(x) for x in PTS if x[1] <= depth)

def pw(s, k):
    return [s] * k if k >= 0 else [s.upper() if s[0] == 'g' else s] * (-k)

def a_(j):  # a_j = alpha^(g1^-j) = g1^j alpha g1^-j
    return pw('g1', j) + ['a'] + pw('g1', -j)

def rho(j):  # rho_j = g2^(g1^-j) = g1^j g2 g1^-j
    return pw('g1', j) + ['g2'] + pw('g1', -j)

ok = True
def check(name, cond):
    global ok
    ok &= cond
    print(('OK  ' if cond else 'FAIL') + ' ' + name)

check('g1 g2 g1^-1 g2^-1 = alpha', eq(word(['g1', 'g2', 'G1', 'G2']), G['a']))
for j in range(-6, 7):
    check(f'a_{j} swaps positions {j},{j+1}', eq(word(a_(j)), trans(pos(j), pos(j + 1))))
    check(f'rho_{j} = a_{j} rho_{j+1}', eq(word(rho(j)), word(a_(j) + rho(j + 1))))
for j in range(-4, 5):
    for d in range(-8, 9):
        conj = word(([{'g1': 'G1', 'G1': 'g1', 'g2': 'G2', 'G2': 'g2', 'a': 'a'}[s] for s in rho(j)[::-1]] + a_(d) + rho(j)))
        if d >= j + 1:
            check(f'a_{d}^rho_{j} = a_{d-1}', eq(conj, word(a_(d - 1))))
        elif d <= j - 2:
            check(f'a_{d}^rho_{j} = a_{d}', eq(conj, word(a_(d))))
# route conversion: alpha^(rho_0^-k) = a_k, and g1^-k g2^k = lambda_(2,3)^k times reversal
for k in range(1, 8):
    w = ['g2'] * k + ['a'] + ['G2'] * k  # alpha^(g2^-k) = g2^k alpha g2^-k
    check(f'alpha^(g2^-k) = a_{k} (k={k})', eq(word(w), word(a_(k))))
T3 = trans((3, 1), (3, 2))
for i in range(-4, 4):
    for j in range(i + 1, 6):
        lhs = word(rho(i) + rho(j))
        rhs0 = word(rho(j + 1) + rho(i))
        check(f'rho_{i} rho_{j} = rho_{j+1} rho_{i} ((3,1),(3,2))', eq(lhs, lambda x: T3(rhs0(x))))
check('D(lambda_(1,2)) = lambda_(1,2)^2 ((2,1),(2,2)) on doubled points',
      all(((lambda y: (y[0], 2 * y[1] - 1))(g1(x)) == trans((2, 1), (2, 2))(g1(g1((x[0], 2 * x[1] - 1)))))
          and ((lambda y: (y[0], 2 * y[1]))(g1(x)) == trans((2, 1), (2, 2))(g1(g1((x[0], 2 * x[1])))))
          for x in PTS if x[1] <= 20))
print('ALL OK' if ok else 'SOME FAILURE')
