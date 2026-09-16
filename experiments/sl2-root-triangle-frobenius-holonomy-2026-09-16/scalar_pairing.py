# scalar_pairing.py -- checks for sl2-root-triangle-tensor-reps-iff-zero-holonomy (2026-09-16).
# Pure python3 + sympy, single-threaded, runs in seconds.  Usage: python3 scalar_pairing.py
# Case 2*hol = 0 != hol (f even, hol = f/2 = h, r = 2^h = sqrt(q)).
# (1) Exponent lemma: for e in {1-r, q-r, 1-qr, q-qr}, gcd(e(q-1), q^2-1) = q-1, so w^e in k* forces w in k.
# (2) Field check for f = 4 (F_256 = F_2[x]/(x^8+x^4+x^3+x^2+1)): for every s in F \ k and every t in Z/8,
#     none of s^(2^t)/s^(2^(t+h)), s^(2^t)/s^(2^(t+h+f)), s^(2^(t+f))/s^(2^(t+h)), s^(2^(t+f))/s^(2^(t+h+f))
#     lies in k = F_16.
# (3) Operator identities on (K^2)^{tensor 4}, slots a = 0, b = 2 (h = 2):
#     [y_a, B x_a + G y_b + D x_a y_b] = B*1 + D y_b;  [x_b, B x_a + G y_b] = G*1;
#     [B x_a + G y_b, B2 x_b + G2 y_a] = (B G2 + G B2)*1   (all mod 2).
from math import gcd
import sympy as sp

# (1)
for f in (4, 6, 8, 10, 12):
    q = 2 ** f; r = 2 ** (f // 2); n = q * q - 1
    ok = all(gcd((e * (q - 1)) % n, n) == q - 1 for e in (1 - r, q - r, 1 - q * r, q - q * r))
    print(f"(1) f={f}: gcd(e(q-1), q^2-1) = q-1 for all four exponents: {ok}")

# (2)
MOD = 0x11D
def gmul(a, b):
    p = 0
    while b:
        if b & 1: p ^= a
        a <<= 1
        if a & 0x100: a ^= MOD
        b >>= 1
    return p
def gpow(a, e):
    e %= 255
    p = 1
    while e:
        if e & 1: p = gmul(p, a)
        a = gmul(a, a); e >>= 1
    return p
def frob(a, t): return gpow(a, pow(2, t % 8))
def ginv(a): return gpow(a, 254)
f, h = 4, 2
k = [w for w in range(256) if gpow(w, 16) == w]
kset = set(k)
bad = 0; tested = 0
for s in range(256):
    if s in kset: continue
    for t in range(8):
        for ta in (t, t + f):
            for tb in (t + h, t + h + f):
                tested += 1
                if gmul(frob(s, ta), ginv(frob(s, tb))) in kset: bad += 1
print(f"(2) f=4: |k| = {len(k)}; {tested} ratios tested, {bad} lie in k")

# (3)
def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]
def slot(op, c, f):
    M = [[1]]
    for t in range(f):
        M = kron(M, op if t == c else [[1, 0], [0, 1]])
    return M
def mm(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def lin(*pairs):
    n = len(pairs[0][1])
    return [[sum(c * M[i][j] for c, M in pairs) for j in range(n)] for i in range(n)]
def comm(A, B):
    AB, BA = mm(A, B), mm(B, A)
    return [[AB[i][j] - BA[i][j] for j in range(len(A))] for i in range(len(A))]
def eq_mod2(A, B):
    return all(sp.Poly(sp.expand(A[i][j] - B[i][j]), *syms, modulus=2).is_zero
               for i in range(len(A)) for j in range(len(A)))
E12 = [[0, 1], [0, 0]]; E21 = [[0, 0], [1, 0]]
B, G, D, B2, G2 = sp.symbols("B G D B2 G2"); syms = (B, G, D, B2, G2)
f, a, b = 4, 0, 2
x = lambda c: slot(E21, c, f); y = lambda c: slot(E12, c, f); I = slot([[1, 0], [0, 1]], 0, f)
z = lin((B, x(a)), (G, y(b)), (D, mm(x(a), y(b))))
print(f"(3) [y_a, z] = B + D y_b: {eq_mod2(comm(y(a), z), lin((B, I), (D, y(b))))}")
z0 = lin((B, x(a)), (G, y(b)))
print(f"(3) [x_b, B x_a + G y_b] = G: {eq_mod2(comm(x(b), z0), lin((G, I)))}")
z1 = lin((B2, x(b)), (G2, y(a)))
print(f"(3) [B x_a + G y_b, B2 x_b + G2 y_a] = B G2 + G B2: {eq_mod2(comm(z0, z1), lin((B * G2 + G * B2, I)))}")
