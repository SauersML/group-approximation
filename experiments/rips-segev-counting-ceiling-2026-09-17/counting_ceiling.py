#!/usr/bin/env python3
"""Window-criterion ceiling for port-cycle counting (rips-segev-port-cycle-counting-has-n-independent-ceiling).

[8C] Lemma 3: under (H_N) no window with E* <= 39 has n* + max(0, e* - N) >= 2N, where
  n* = b-syllables met by the window (partial ends included),
  e* = whole b^2-syllables inside it,
  E* = n* + e* = b-edges of the window.
A window is: an optional partial first syllable (one edge of a b^2), t1 whole single b's,
t2 whole b^2's, and an optional partial last syllable.  Only these counts matter.

Checks:
 (1) over all windows, max n* + max(0, e* - N) = 39 for every N, so the criterion is vacuous for N >= 20;
 (2) on an all-b^2 face (every b-syllable b^2, e.g. the relator of the directed cycle (x_4 x_1)^21,
     l = 42, 42 b-edges) the max is below 2N exactly for N >= 14;
 (3) with an active-coset bound A(N) = c N + d, the contradiction L <= A(N) < L_0 = 42 holds only
     for N < (42 - d)/c.
"""


def window_values(N, all_b2=False, cap=39):
    """Yield (n*, e*, E*, value) for every window type with E* <= cap."""
    for p in range(3):              # number of partially covered end syllables (each one edge)
        for t2 in range(cap // 2 + 1):
            for t1 in range(cap + 1):
                if all_b2 and t1:
                    continue
                E = t1 + 2 * t2 + p
                if E > cap or E == 0:
                    continue
                n = t1 + t2 + p
                e = t2
                assert n + e == E
                yield n, e, E, n + max(0, e - N)


def best(N, all_b2=False):
    return max(window_values(N, all_b2), key=lambda r: r[3])


def cyclic_face_best(N, exps, cap=39):
    """Exact max over all windows (contiguous b-edge runs, E* <= cap) of a cyclic face with
    b-syllable exponents `exps`."""
    edges = []                      # (syllable index, exponent) per b-edge
    for j, x in enumerate(exps):
        edges += [(j, x)] * x
    m = len(edges)
    top = -1
    for start in range(m):
        for E in range(1, min(cap, m - 1) + 1):
            run = [(start + k) % m for k in range(E)]
            count = {}
            for k in run:
                count[edges[k][0]] = count.get(edges[k][0], 0) + 1
            n = len(count)
            e = sum(1 for j, c in count.items() if exps[j] == 2 and c == 2)
            assert n + e == E
            top = max(top, n + max(0, e - N))
    return top


def main():
    print("(1) all windows, E* <= 39")
    for N in range(1, 26):
        n, e, E, v = best(N)
        assert v == 39, (N, v)
    print("    max n* + max(0, e* - N) = 39 for N = 1..25 (attained at e* = 0)")
    print("    criterion needs >= 2N; 39 >= 2N iff N <= 19; vacuous for all N >= 20")

    print("(2) all-b^2 face, E* <= 39")
    face = [2] * 21                 # (x_4 x_1)^21: 21 syllables b^2, 42 b-edges
    last_live = None
    for N in range(1, 26):
        n, e, E, v = best(N, all_b2=True)
        exact = cyclic_face_best(N, face)
        assert exact == v, (N, exact, v)
        live = v >= 2 * N
        if live:
            last_live = N
        print(f"    N={N:2d}: max {v:2d} (n*={n}, e*={e}, E*={E}) vs 2N={2*N:2d} -> "
              f"{'window exists' if live else 'vacuous'}")
    assert last_live == 13
    print("    all-b^2 faces escape the criterion for every N >= 14")

    print("(3) linear active-coset bounds against the one-face floor L_0 = 42")
    for c in (1, 2, 3, 4, 7):
        for d in (0,):
            closable = [N for N in range(1, 200) if c * N + d < 42]
            print(f"    A(N) = {c}N + {d}: L <= A(N) < 42 only for N <= {max(closable)}")


if __name__ == "__main__":
    main()
