# Lane hl-surface-girth-general: surface subgroups in all hyperbolic KMS families (2026-09-14)

Target: Gromov's surface subgroup question for hyperbolic Kazhdan groups
(`one-ended-hyperbolic-groups-contain-surface-subgroups`). Starting point: lane hl-surface-subgroups covered four of
the six hyperbolic KMS families of Caprace–Conder–Kaluba–Witzel; `G_HC2(1)` and `G_HBC2(2)` resisted, and orientable
classes 42 and 51 of `G_HB2(2)(7)` had no labelling for unexplained reasons.

## Results

1. `kms-vertex-words-close-iff-weights-have-zero-height-moments` (ESTABLISHED, proof route with no imports). An
   alternating word `x^{a_1} y^{b_1} ⋯ x^{a_m} y^{b_m}` in `U_3(p)` or `U_4(p)` is trivial exactly when
   `Σ b = 0` and `Σ_r a_r H_r^d = 0` for `d ≤ m − 2`, with heights `H_r = b_1 + ⋯ + b_{r−1}`.
   - With nonzero exponents: Lagrange weights at distinct heights, plus in `U_4` the alternating words
     `a = (a_1, a_2, −a_1, −a_2)`, `b = (d, −d, d, −d)`.
   - Counts `(p−1)^2 (p−2)` and `(p−1)^2 ((p−2)(p−3) + (p−1))`; checked for `p ≤ 13` (`check-moment-lemma.log`).
2. `kms-hbc2-groups-contain-genus-two-surface-subgroups` (ESTABLISHED, computer-certified):
   `G_HBC2(2)(p)` for `p = 5` and every prime `p ≥ 7`.
   - Surface 67 (24 chambers) has an integer labelling with labels in `[−6, 6]`, divisible only by 2, 3, 5.
   - `p = 5`: an `F_5` labelling of surface 67.
3. `kms-hc1-groups-contain-genus-two-surface-subgroups` (ESTABLISHED, computer-certified): `G_HC2(1)(p)` for every
   prime `p ≥ 5`, via surface 190 of the 191 girth surfaces with 48 chambers, labels in `[−4, 4]`.
4. With the landed nodes for `G_HB2(2)`, `G_HC2(2)`, `G_HB2(3)`, `G_HBC2(3)`: **all six hyperbolic KMS families contain
   quasiconvex genus-two surface subgroups for every prime `p ≥ 5`**. Every KMS group over `F_p` that CCKW Corollary 7.8
   shows to be Kazhdan (`p ≥ 7` or `p ≥ 11`) is covered.

Nothing here is reviewed. "New" means not found on main or in the sources hl-surface-subgroups searched.

## How the resistant families fell

- The landed integer search listed allowed vertex-word tuples by brute force over `{±1, ±2, ±3}^{2m}`. The moment
  lemma lists trivial words from heights instead, which reaches `|x| ≤ 15` cheaply. The enumerator of `intsearch.py`
  agreed with brute force for the vertex kinds of `G_HB2(2)`, `G_HBC2(2)`, `G_HC2(1)` and `G_HB2(3)` at `N = 2, 3`. That
  was a local one-off check and is not landed; every certificate is re-verified independently anyway.
- **Calibration.** `explore.py` (normal-form law mod `p`) reproduces the landed `F_7` counts of `G_HB2(2)(7)` exactly:
  surfaces 17, 29, 53, 42, 51, 25, 31, 43 give `216, 1944, 432, 0, 0, 5184, 3456, 6912`, with the same search-node
  counts as `ghb7_girth_surfaces.py` (`logs/calib-hb2-p7.log`). `int-hb2-n2-control` recovers surface 67 of
  `G_HB2(2)`; `int-hbc2-n3-control` reproduces the landed negative for `G_HBC2(2)`.
- `G_HBC2(2)`, 24 chambers: `F_7` labellings exist on surfaces 65, 67 (orientable) and 71; `F_5` on 67 and 5; none over
  `F_3`. Integer labellings of surface 67 exist with `|x| ≤ 6`, `10`, `15`, and all use labels divisible by 3 and 5.
  None with absolute values in `{1,2,4,8}`, `{1,2,4,7,8}` (surfaces 65, 67, 71) or `{1,2,4,8,16}` (65, 67).
- `G_HC2(1)`: 24 chambers (5 surfaces, all non-orientable) give nothing over `F_5`, `F_7` or with `|x| ≤ 6`. At 48
  chambers, surface 190 with `|x| ≤ 4`. Surface 190 has no `F_3` labelling and none with absolute values in
  `{1, 2, 4}` or `{1, 2, 4, 8}`.
- Verification: the landed integral matrix verifier for the integer certificates; `verify_modp.py` (matrix products
  mod `p`, no shared code) for `F_p` certificates, with a corrupted-label control that fails.

## The zero counts of `G_HB2(2)(7)` (OPEN)

Classes 42 and 51 are orientable and have no labelling over `F_7` or `F_5` (`logs/feas-hb2-t24-p5.log`). Relaxation
data over `F_7` (`logs/cores-hb2-p7.log`). "Heisenberg" means dropping the cubic coordinate `ν` at `U_4` vertices;
"abelian" means keeping only exponent sums.

| relaxation | surface 42 | surface 51 |
|---|---|---|
| full conditions | UNSAT | UNSAT |
| all vertices Heisenberg | SAT | SAT |
| all vertices abelian | SAT | SAT |
| drop any one of the 4 `U_3` vertices | SAT | UNSAT |
| drop any one of the 6 `U_4` vertices | SAT | SAT |
| relax any one `U_4` vertex to Heisenberg | SAT | UNSAT (vertices 4–9) |
| greedy minimal vertex core | all 10 vertices | vertices 1–9 |
| in that core, relax to Heisenberg | every `U_4` vertex unlocks | vertices 4, 7 unlock; 5, 6 do not |

- For surface 42 the obstruction is global and cubic. Each single cubic condition can be met once any other is
  dropped, and removing any vertex (a hole) lifts it. That is the signature of a Stokes-type identity among the cubic
  conditions that forces a nonvanishing quantity. No such identity was derived.
- Surface 51 behaves differently: the core needs whole `U_4` vertices, not just their cubic coordinates.

**Potential formulation (derived, not landed as a claim).** Given the exponent-sum conditions, a labelling of a
girth surface `S` is the same as potentials `φ_k` on the type-`k` vertices of the universal cover `S̃`, well defined
because `S̃` is simply connected. The label on a type-`k` side is the difference of `φ_k` at the two apexes of that
side. `π_1(S)` acts through translations (periods in `H^1(S; F_p)`).
- At a vertex `v` of type `i`, with designated type `x` and third type `y`, the vertex condition becomes
  `Σ_σ Δ_σ φ_x · φ_y(w_σ)^d = 0` for `d ≤ m_i − 2`. The sum runs over the type-`x` sides `σ` at `v`, and `w_σ` is the
  type-`y` endpoint of `σ`.
- For `G_HB2(2)`: `φ_1` is constant around type-2 vertices, and `φ_2` around type-1 vertices.
- So the area conditions at all vertices of a given type sum, by discrete Stokes over a fundamental domain, to a
  cup product of periods (sketched, not written out).
- With trivial periods, a surface with 24 chambers has only three type-1 and three type-2 vertices. Every octagon is
  then forced into the alternating family, so generic octagons need nontrivial periods.

## Gaps

1. **`p = 3`** for `G_HBC2(2)` (no `F_3` labelling at 24 chambers) and `G_HC2(1)` (surface 190 none over `F_3`).
   Next: larger surfaces at `p = 3`, where only alternating octagons exist.
2. **Zero counts.** The cubic Stokes identity for surface 42 and the core structure of surface 51.
   - The moment lemma plus potentials is the handle: sum `∮ φ_y^2 dφ_x` over vertices of one type.
   - The obstruction persists at `p = 5` and `p = 7`.
3. **Structural existence.** The families are covered by specific certificates, not by an argument that works for
   every generalized triangle group with CAT(−1) links. Not attempted:
   - point counts over `F_q` as polynomials in `q`;
   - KMS groups over `F_q`, `q = p^e` (the vertex groups change, and the criterion was proved for prime fields only).
4. **Commutator words.** For the five families other than `G_HB2(2)` they come from the CCKW text extraction
   (`kms-girth-surfaces-give-surface-subgroups`), so the new instances inherit that caveat.

## Files and jobs

- `experiments/kms-surface-girth-general/`:
  - `explore.py`, `cert.py`, `intsearch.py`, `intsearch2.py`, `verify_modp.py`, `check_moment_lemma.py`;
  - `certificates/`, the `verify-*.log` files and `logs/`.
- MSI jobs 792226 (calibration, cores, feasibility), 793113 (feasibility at other primes, still running at landing
  time), 793431 (`F_7` certificates), 793895 (integer search), 794384 (moment check, `F_5` certificates),
  794523 (restricted and `G_HC2(1)` searches), 794742 (`F_3`), 794966 (`G_HC2(1)` at `p = 3`).
- Files under `/scratch.global/sauer354/hl-surface-girth-general/`.
