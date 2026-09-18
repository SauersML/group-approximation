"""Regimes of the sibling-cube problem: forced drop, staggered filling, or open.

N swap nodes with projective dimensions j_1..j_N and Toms's twists (alpha^k != beta^k).
  D = N^2 + 2N - 2   (the band space X_(g,N) is D-connected; H_(D+1) = Z)
  d = N + 2 sum j    (dimension of the cube family S x Y)

  forced   : Hall condition #{nu : j_nu <= J} <= J for all J  (cube theorem,
             toms-sibling-cube-swap-drops-add-to-depth-n)
  fill     : d <= D + 1                                   (Theorem B)
             d == D + 2 and multiset {j} != {1..N}         (Theorem C)
  open     : otherwise

Checks: (i) the regimes never overlap; (ii) at d == D + 2 the two criteria agree, i.e.
Hall holds iff {j} = {1..N}; (iii) the alternant det[u_nu^k] in top degree of prod CP^(j_nu)
is non-zero iff {j} = {1..N} (brute force over permutations); (iv) the equal-dimension table
forced iff N <= j, fill iff N >= 2j - 1 (except (1,1)), open iff j+1 <= N <= 2j-2.
Run: python3 filling_table.py  (prints a JSON summary).
"""
import itertools
import json


def hall(js):
    s = sorted(js)
    return all(s[i] >= i + 1 for i in range(len(s)))


def alternant_top_nonzero(js):
    """Is det[u_nu^k]_(k,nu=1..N) non-zero in Q[u]/(u_nu^(j_nu+1)) (any degree)?"""
    N = len(js)
    for pi in itertools.permutations(range(1, N + 1)):
        if all(pi[nu] <= js[nu] for nu in range(N)):
            return True  # monomials are distinct, so one surviving monomial suffices
    return False


def regime(js):
    N = len(js)
    D = N * N + 2 * N - 2
    d = N + 2 * sum(js)
    forced = hall(js)
    if d <= D + 1:
        fill = True
    elif d == D + 2:
        # alternant non-zero iff a bijection k -> nu with k <= j_nu exists (checked by
        # brute force against alternant_top_nonzero for N <= 5 in main)
        fill = not hall(js)
    else:
        fill = False
    assert not (forced and fill), js
    return "forced" if forced else ("fill" if fill else "open")


def main():
    checks = {"overlap_free": True, "D+2_agreement": 0, "alternant_vs_hall": 0}
    for N in range(1, 6):
        for js in itertools.combinations_with_replacement(range(1, 8), N):
            r = regime(js)
            D = N * N + 2 * N - 2
            if N + 2 * sum(js) == D + 2:
                assert hall(js) == (sorted(js) == list(range(1, N + 1)))
                checks["D+2_agreement"] += 1
            assert alternant_top_nonzero(js) == hall(js)
            checks["alternant_vs_hall"] += 1
    table = {}
    for j in range(1, 9):
        row = {}
        for N in range(1, 20):
            r = regime((j,) * N)
            row[N] = r
            if N <= j:
                assert r == "forced"
            elif N >= 2 * j - 1:
                assert r == "fill"
            else:
                assert r == "open"
        table[j] = "".join({"forced": "F", "fill": ".", "open": "?"}[row[N]] for N in range(1, 20))
    toms = {}
    for dn in range(1, 4):
        j = 2 * dn * dn
        toms[dn] = {"j_n": j, "forced_up_to_N": j, "open_N": [j + 1, 2 * j - 2],
                    "fill_from_N": 2 * j - 1}
    out = {"checks": checks,
           "equal_dims_table (N = 1..19; F forced, . fill, ? open)": table,
           "toms_bottom_level": toms}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
