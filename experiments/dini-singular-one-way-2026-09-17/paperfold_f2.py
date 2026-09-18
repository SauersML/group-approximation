"""Reversal collisions of the inverse-paperfolding code in F_2 = <a,b>.

Code: U_0 = a, U_n = U_{n-1} t_n U_{n-1}^{-1}, t_n in {b, b^-1} fair coins.
Letter at position p (1-indexed), p = 2^j * o (o odd): X_j^{eps}, X_0 = a, X_j = t_j,
eps = +1 if o = 1 mod 4 else -1 (paperfolding).  lambda = law of the ray.
In the Cayley tree O_s(g) = cylinder [g minus its last s letters], so
S_s(lambda) = sum_{|q|=|z|=s, r} lambda[q r] lambda[z^-1 r^-1]  (reduced words),
i.e. level l = |r| collides when some code prefix P (|P| = s+l) and code prefix Q
(|Q| = s+l) satisfy P[s:]^{-1} = Q[s:].
Prints, per s, the collision levels l and the partial sums of S_s.
"""
import sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
N = 2**K - 1                       # prefixes of length <= N are determined by t_1..t_{K-1}
INV = bytes.maketrans(b'aAbB', b'AaBb')

def ray(bits):                     # bits[j-1] = 0 -> t_j = b, 1 -> B
    out = bytearray()
    for p in range(1, N + 1):
        j, o = 0, p
        while o % 2 == 0:
            o //= 2; j += 1
        pos = (o % 4 == 1)
        if j == 0:
            out += b'a' if pos else b'A'
        else:
            tb = bits[j - 1]
            up = (tb == 0) == pos
            out += b'b' if up else b'B'
    return bytes(out)

rays = [ray([(m >> i) & 1 for i in range(K)]) for m in range(2 ** (K - 1))]
def mass(n):                       # prefix of length n is fixed by t_j with 2^j <= n
    return 2.0 ** (-(n.bit_length() - 1)) if n >= 1 else 1.0

for s in range(0, 4):
    levels, S = [], 0.0
    for l in range(1, N - s + 1):
        n = s + l
        prefs = {r[:n] for r in rays}
        tails = {}
        for P in prefs:
            tails[P[s:]] = tails.get(P[s:], 0) + 1
        hit = 0.0
        for P in prefs:
            key = P[s:].translate(INV)[::-1]
            c = tails.get(key)
            if c:
                hit += mass(n) * mass(n) * c
        if hit > 0:
            levels.append(l); S += hit
    print(f"s={s}: collision levels l (l+1 shown) = {[x + 1 for x in levels]}")
    print(f"s={s}: partial S_s up to level {N - s} = {S:.6f}")
