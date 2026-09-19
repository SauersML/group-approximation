# Quaternionic representations and cone certificates for 31_30 #26 and 31_31 #12

These are the artifacts of `research/bmw-klein-free-quaternionic-parity-kernels.md`, whose proof is in
`-proof.md`. The census files are read from `experiments/bmw-census-left-orders-2026-09-17/`. Give
them as bare file names.

## Checkers (independent, exact)

- `verify_quat_rep.py`: no arguments. It uses sympy over GF(2) and its own structure constants for
  `D = [t, t²+t+1)`, not `quat.py` or `gf2poly.py`. It checks:
  - associativity;
  - the Gram determinant `b²`;
  - that `D` is ramified at `b`;
  - all relations of both groups, up to scalars;
  - the tree conditions (T1) and (T2) at `t` and `t+1`.

  Output: `verify_quat_rep.log`.
- `verify_cone.py census.json class tree.json`: checks a cone-propagation certificate. It uses only
  the census squares, its own rewriting normal form and a Newman critical-pair check. Output:
  `verify_cone.log`, which records 6 leaves and 54 product steps for each class.

**Mutation test.** In `REPS` of `verify_quat_rep.py`, exchange `v_1` and `v_2` for #26. The square
check then fails with an `AssertionError`, as it should.

## Search scripts (not needed for the proof)

- `findquat.py census.json class d a b PV PH`: searches for `ρ` into `[a, b)`, with coordinates of
  degree at most `d`, where the h-letters move the vertex at `PH` and the v-letters the vertex at
  `PV` (place `0` is `t`, place `1` is `t+1`). Polynomials are ints (bit `i` is the coefficient
  of `t^i`).
  - `findquat.py census_31_31.json 12 1 2 7 0 1` prints two representations. The first is the one in the claim.
  - `findquat.py census_31_30.json 26 2 2 7 0 1` prints two representations for #26. The one in the
    claim is among them, and its `v_1` has degree 2.

  It uses `quat.py` (the arithmetic of `[a, b)`) and `gf2poly.py` (`F_2[t]` as ints).
- `dtree.py census.json class R maxdepth`: finds the smallest cone-propagation tree on the radius-`R`
  ball, using `lo_census`.
  - `R = 4` and `maxdepth = 3` produce `tree_31_30_26.json` and `tree_31_31_12.json`.
  - Each file has "no tree of depth 1" and "no tree of depth 2", then the certificate as JSON.
- `levels.py census.json class N`: orders of the action of `⟨A⟩` on the levels of `T_v`.
- `tori.py census.json class L`: fixed-letter graph and the shortest inverters of pure words, which
  are involution letters.

All runs are single-threaded, take under a minute, and use under 200 MB.
