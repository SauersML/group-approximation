"""Controls for the SAT encoding (one-vertex 2-graphs with 4 edges of each colour).

product: the square bijection (e_i f_j) = (f_j e_i) (product of two 4-loop graphs);
         its cylinder-exchange group is a Brin-Thompson-type group, and a brick coding
         exists in dimension 2 (phi(e_i) = (i in binary, ''), phi(f_j) = ('', j in binary)).
twisted: the square bijection (e_i f_j) = (f_j e_{i+j mod 4}), a genuine bijection of
         composable pairs.  Printed for information.
For one-vertex 2-graphs with no nontrivial relations among squares, H^1 is large, so
Proposition B does not apply and uniform=True is only a restricted search for these.
"""
import brick_sat, rs2graph


def fake_build(squares_map):
    tiles = [0]
    E1 = [(0, 0)] * 4
    E2 = [(0, 0)] * 4
    sq = [(i, j) + squares_map(i, j) for i in range(4) for j in range(4)]
    assert len({s[2:] for s in sq}) == 16  # square map is a bijection
    return tiles, E1, E2, sq


if __name__ == "__main__":
    for name, mp in [("product", lambda i, j: (j, i)),
                     ("twisted", lambda i, j: (j, (i + j) % 4))]:
        rs2graph.build = lambda T, mp=mp: fake_build(mp)
        for m in (1, 2):
            r = brick_sat.solve(None, m, uniform=True)
            print(name, "m =", m, "SAT" if r else "UNSAT", r[4] if r else "", flush=True)
