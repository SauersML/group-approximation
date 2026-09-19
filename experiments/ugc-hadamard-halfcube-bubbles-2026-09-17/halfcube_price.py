"""Exact edge prices of the half-cube bubble adversary for Had_k.

Setting (notation of hadamard-gadget-deletion-ratio-window): K = 2^k,
Q = {-1,1}^K indexed by F_2^k, chi_a(z) = (-1)^(a.z), W_a(x) = <x, chi_a>.

Adversary H_t (t an integer, 0 <= t <= K/2 - 1), given uniform pins xi:
  * i uniform in F_2^k and tau = +-1 uniform, independent of xi;
  * B = {a : xi_a != tau chi_a(i)} (the bad primaries); given (i, tau)
    B is a uniform random subset, since xi is uniform;
  * e_a(x) = (K - x_i chi_a(i) W_a(x)) / 2, the distance from x to the
    signed pin x_i chi_a(i) chi_a lying in x's own half {z : z_i = x_i};
  * H_t(x) = -tau x_i if min_{a in B} e_a(x) <= t, else tau x_i.
H_t is folded (e_a(-x) = e_a(x)) and meets every pin because t < K/2.
A mixture over t with weights q_t is again folded and random on P.

For an edge (x, y = x with coordinate j flipped), K Pr[cut] = sum_i Pr_B[cut | i],
and with S_x = {a : e_a(x) <= t}, S_y likewise (using y's own half),
U = S_x | S_y:
  i != j : cut iff exactly one of x, y is flipped:
           2^-|S_x| + 2^-|S_y| - 2 * 2^-|U|
  i == j : y is in the other half, cut iff both or neither are flipped:
           2^-|U| + 1 - 2^-|S_x| - 2^-|S_y| + 2^-|U|
The price is invariant under x -> -x and x -> x chi_b, so it suffices to
take x = +1 on {0, e_1, ..., e_k}.
"""
from fractions import Fraction
import itertools, sys


def chars(k):
    K = 1 << k
    return [[-1 if bin(a & z).count("1") % 2 else 1 for z in range(K)] for a in range(K)]


def walsh(x, ch):
    return [sum(xa * ca for xa, ca in zip(x, c)) for c in ch]


def prices(x, j, k, ch):
    """Return list C[t] (Fractions) of K*Pr[cut] for H_t on edge (x, x^j)."""
    K = 1 << k
    y = list(x)
    y[j] = -y[j]
    Wx, Wy = walsh(x, ch), walsh(y, ch)
    out = [Fraction(0)] * (K // 2)
    for i in range(K):
        ex = [(K - x[i] * ch[a][i] * Wx[a]) // 2 for a in range(K)]
        ey = [(K - y[i] * ch[a][i] * Wy[a]) // 2 for a in range(K)]
        for t in range(K // 2):
            sx = sum(1 for a in range(K) if ex[a] <= t)
            sy = sum(1 for a in range(K) if ey[a] <= t)
            su = sum(1 for a in range(K) if ex[a] <= t or ey[a] <= t)
            px, py, pu = Fraction(1, 2 ** sx), Fraction(1, 2 ** sy), Fraction(1, 2 ** su)
            if i != j:
                out[t] += px + py - 2 * pu
            else:
                out[t] += 2 * pu + 1 - px - py
    return out


def reps(k):
    K = 1 << k
    info = {0} | {1 << m for m in range(k)}
    free = [z for z in range(K) if z not in info]
    for bits in itertools.product((1, -1), repeat=len(free)):
        x = [1] * K
        for z, b in zip(free, bits):
            x[z] = b
        yield x


def all_price_vectors(k):
    ch = chars(k)
    K = 1 << k
    seen = set()
    for x in reps(k):
        for j in range(K):
            seen.add(tuple(prices(x, j, k, ch)))
    return sorted(seen)


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    vecs = all_price_vectors(k)
    print("k", k, "distinct price vectors", len(vecs))
    for t in range((1 << k) // 2):
        print("pure t =", t, "max price", float(max(v[t] for v in vecs)))
