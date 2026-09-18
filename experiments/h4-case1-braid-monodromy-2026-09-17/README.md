# Braid monodromy of the fibred H_4 augmentations (lane w6-042, 2026-09-18)

This directory supports `research/h4-a2-fibred-shadows-are-a4-pure-braid-retractions.md`. Both scripts import
`fibred.py` from `../h4-case1-fibred-quotient-2026-09-17/` (lane w5-042). They use numpy only and finish in
seconds.

- `arrangement.py` → `arrangement.log`. It checks each of the 9 `A_2` flats `V` of `H_4`:
  - the 4 fibre normals are independent;
  - the 6 collision walls are 3 walls of `A_z` and 3 walls of `A_x∖A_z`;
  - so the 10-wall sub-arrangement `C_V` is linearly the `A_4` braid arrangement, and it is not
    reflection-closed;
  - the real order is `p4 < p1 < p2 < p3 < t` near both `x*` and `y*`;
  - the `p4`-collision walls cover all 12 walls of `A_x∖A_z`.

  It runs the same check on the 2 `A_2` flats of `H_3`, which give `A_3`.
- `i25probe.py` → `i25probe.log`. It computes the three fibred `I_2(5)` flats of `H_4`:
  - 6 fibre points, with fibre normals of rank 4;
  - 10 collision walls, with characteristic polynomial `(t-1)(t-4)(t-5)`;
  - two modular lines of 5 walls each.

Conclusion: the braid monodromy `mu : P_X → P_4` of each `A_2` shadow kills 9 of the 15 meridians and sends the
other 6 to the meridians `A_ij`. The shadow is the retraction `P ↠ P_5` onto an `A_4` braid arrangement. So
the point-pushing identity in one `A_2` shadow is exactly the `A_4` single-edge hexagon relation.

Run with `python3 arrangement.py > arrangement.log` and `python3 i25probe.py > i25probe.log`.

## I_2(5) flats: rigid pentagon cluster

`i25cluster.py` → `i25cluster.log` supports `research/h4-i25-fibred-shadows-are-rigid-cluster-braid-groups.md`.
For each of the three fibred `I_2(5)` flats it checks:
- the `A_y` fibre point on `w`, together with the 3 new fibre points, has normals of rank 2;
- all 6 pairs of that cluster collide on the one wall `w'` of `V` through `l_x`; every other collision is a
  single pair;
- the cluster shape is `p_c + s·{0, 1, 1/phi, phi}`, and the 5 normals lie at `18, 54, 90, 126, 162` degrees;
- the real order at the base point is `q q q p1 p2 p3 t`.

The shadow is therefore `f^{-1}(<Delta^2_C>) ⊂ P_7`, where `f` forgets `t, p_a, p_b`. Run with
`python3 i25cluster.py > i25cluster.log`.
