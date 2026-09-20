"""Check the combinatorial facts behind R*(k) <= R*(k+1) (diagonal restriction).

iota: {+-1}^{F_2^k} -> {+-1}^{F_2^{k+1}}, iota(y)_(i,u) = y_i.
Checks, exhaustively for k = 1, 2, 3:
  (1) iota(-y) = -iota(y)                      (folding preserved)
  (2) iota(chi_a) = chi_(a,0), and a != 0 => (a,0) != 0   (pins -> pins)
  (3) iota injective, so f o iota of a uniformly random pattern is uniform
  (4) for every y and every coordinate j, iota(y) and iota(y^j) are at
      Hamming distance exactly 2, joined through iota(y) with (j,0) flipped.
Coordinates of F_2^{k+1} are encoded as i + u*2^k.
"""
import itertools

def chi(a, K):
    return tuple(1 - 2 * (bin(a & i).count("1") & 1) for i in range(K))

for k in (1, 2, 3):
    K = 2 ** k
    iota = lambda y: tuple(y[x % K] for x in range(2 * K))
    for a in range(K):
        assert iota(chi(a, K)) == chi(a, 2 * K)            # (a,0) has index a
    seen = set()
    for y in itertools.product((1, -1), repeat=K):
        Y = iota(y)
        assert iota(tuple(-v for v in y)) == tuple(-v for v in Y)
        seen.add(Y)
        for j in range(K):
            yj = list(y); yj[j] = -yj[j]; Yj = iota(tuple(yj))
            diff = [x for x in range(2 * K) if Y[x] != Yj[x]]
            assert diff == [j, j + K]
            mid = list(Y); mid[j] = -mid[j]
            assert sum(m != v for m, v in zip(mid, Y)) == 1
            assert sum(m != v for m, v in zip(mid, Yj)) == 1
    assert len(seen) == 2 ** K
    print("k", k, "-> k+1: lift checks pass")
