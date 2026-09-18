"""Borel absorption of the depth generators mod p.

a = [[1,2],[0,1]] is upper triangular, so the Borel subgroup B(F_p) (upper
triangular) is absorbing for t -> t a t^-2: once t_j is in B mod p, so is every
later t_j, and the image of L_j = <a, t_j> mod p is solvable (inside
B(F_p) = F_p^* x| F_p). This prints, for each odd prime p < 60, the first depth
j_p with t_j in B mod p (or None up to the eventual period of t_j mod p).
"""
from gen import depth_generator


def mul(x, y, m):
    return ((x[0]*y[0] + x[1]*y[2]) % m, (x[0]*y[1] + x[1]*y[3]) % m,
            (x[2]*y[0] + x[3]*y[2]) % m, (x[2]*y[1] + x[3]*y[3]) % m)


def inv(x, m):
    return (x[3] % m, (-x[1]) % m, (-x[2]) % m, x[0] % m)


def first_borel(p):
    a, t = (1, 2, 0, 1), (1, 0, 2 % p, 1)
    seen = {}
    j = 0
    while t not in seen:
        if t[2] % p == 0:
            return j, None
        seen[t] = j
        ti = inv(t, p)
        t = mul(mul(t, a, p), mul(ti, ti, p), p)
        j += 1
    return None, (seen[t], j - seen[t])


if __name__ == '__main__':
    primes = [p for p in range(3, 60) if all(p % q for q in range(2, p))]
    for p in primes:
        jp, cyc = first_borel(p)
        if jp is not None:
            print(f"p={p}: t_j in Borel mod p from j={jp} on")
        else:
            print(f"p={p}: never Borel; t_j mod p enters a cycle at j={cyc[0]} of length {cyc[1]}")
