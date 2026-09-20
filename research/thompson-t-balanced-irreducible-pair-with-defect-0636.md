---
rg: 2
id: thompson-t-balanced-irreducible-pair-with-defect-0636
kind: claim
title: There is an irreducible exact Z/4 * Z/3 pair in U(12) with balanced spectra and Lochak--Schneps defect below 0.6361, and fixed-spectrum local search does not find it in dimension 24
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that node proves the equivalence "T not MF iff the defect of nontrivial irreducible pairs is bounded below"; this node gives an explicit upper bound for the balanced-spectrum part of that infimum and records where numerical search for it fails.
  thompson-t-has-full-mf-radical: that is the open target (a uniform lower bound on the defect); this gives an explicit upper bound for balanced pairs, so the target's gap in the balanced sector is at most 0.63605.
  thompson-t-pentagon-winding-rigidity: that concerns the winding invariant of low-defect sequences; this is one explicit finite pair plus a search census, with no winding statement.
artifacts:
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/verify_witness.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/witness_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_verify_witness_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/census.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/two_stage.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/analyse.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/planted_double.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/spinor_curve.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/check_planted.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/check_planted_mono.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/control_n2.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/control_planted.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/log_two_stage_bal12b.txt
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_bal24a.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_bal24b.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_sp6.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_sp12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_two_stage_sp24.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_analyse_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_analyse_sp6.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_planted_double_k2_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_planted_mono_k1.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_planted_mono_k3.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_planted_mono_k6.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_spinor_curve.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_control_n2.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_control_planted_n6.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_control_planted_n12.json
---

**ESTABLISHED** by `thompson-t-balanced-irreducible-pair-with-defect-0636-proof`
(a verified float64 computation with an explicit perturbation certificate).
Items 1 and 2 are the established content. Item 3 is a record of searches: it
reports what happened and proves nothing about infima.

## Setting

The notation is that of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`.
An **exact pair** is `(A, B)` in `U(n)^2` with `A^4 = B^3 = 1`. With
`X = BAB`, `J = A^2`, `W = A^2 B^2 A^2` and `W^(-1) = A^2 B A^2`, the relators are

```text
r_1 = [X, J X J],   r_2 = [X, W X W^(-1)],   r_P = (BA)^5,
D(A,B) = max_k ||r_k - 1||      (operator norm).
```

The pair is **balanced** if each eigenvalue of `A` (among `1, i, -1, -i`) has
multiplicity `n/4`, and each eigenvalue of `B` (among `1, w, w^2`, with
`w = e^(2 pi i/3)`) has multiplicity `n/3`. Equivalently, `tr A^j = tr B^j = 0`
for all `j` that are nonzero modulo the order. Balanced pairs are the relevant
sector for the target. Suppose `D -> 0` along a sequence of exact pairs that
converges in tracial distribution to a trace on `C*(T)`. The limit trace has the
form `a·tau_1 + (1-a)·delta_e`, and simplicity of `T` gives this form. If `a = 0`
(the limit is the regular trace), the pairs become asymptotically balanced. This
reduction was posted on the live bus in wave 22 and is not a node in this tree.
It is used here only as motivation.

## Statement

1. **(Explicit balanced witness.)** Let `U` be the `12 x 12` matrix stored in
   `witness_bal12.json`, and let `U~ = U (U^* U)^(-1/2)` be its unitary polar
   part. Put `dA = (1,1,1, i,i,i, -1,-1,-1, -i,-i,-i)` and
   `dB = (1,1,1,1, w,w,w,w, w^2,w^2,w^2,w^2)`. Then

   ```text
   A = U~ diag(dA) U~^*,   B = diag(dB)
   ```

   is an exact balanced pair in `U(12)` with

   ```text
   D(A,B) <= 0.6360452410185    (float value 0.6360452410174; defects 0.63566, 0.63605, 0.63592).
   ```

   All three relators are active at this point. Also
   `||A^2 B A^(-2) B^(-1) - 1|| = 1.376`, so the pair is far from making `A^2` central.
2. **(Irreducible.)** The pair `(A, B)` is irreducible: its commutant is the scalars.
   The operator `X -> ([A,X], [B,X])` on `M_12(C)` has a 1-dimensional kernel, and
   its second-smallest singular value is `0.2380`. So the balanced sector of the
   irreducible-pair infimum satisfies

   ```text
   delta_bal(12k) := inf { D(A,B) : exact balanced pair in U(12k) } <= 0.63605   for every k >= 1,
   ```

   by taking `k`-fold direct sums, since `D` of a direct sum is the max of the `D`s.
   The witness is irreducible, so this bound is not inherited from a smaller
   dimension.

   It also beats every balanced pair that is a direct sum of blocks of
   dimension at most 2; each such pair has `D >= 0.99`. The table
   `out_control_n2.json` gives the minimum of `D` over each 2-dimensional
   spectral class, computed by brute force over the one conjugacy parameter
   and including reducible points. The 1-dimensional characters `(a, b)` have
   `D = |(ab)^5 - 1|`, which can be read off directly.

   In every block with `D < 0.99`, the multiplicity of the eigenvalue
   `B = 1` is at most the multiplicity of `A = 1`:
   - the characters `(a, 1)` with `a != 1` have `D >= 1.414`;
   - the classes `A ~ {i,-i}, B ~ {1,w}` and `A ~ {i,-i}, B ~ {1,w^2}` have
     `D = 1.0008` on the grid (1.0002 from the optimiser);
   - every other class containing `B = 1` with `D < 0.99` also contains `A = 1`.

   A balanced pair has `mult(B = 1) = n/3 > n/4 = mult(A = 1)`, so it needs a
   block with `D >= 0.99`.
3. **(Search census; record, not theorem.)** The search method was fixed-spectrum
   Riemannian descent on `U` with a soft-max loss (`census.py`), followed by a
   monotone polish and basin hopping (`two_stage.py`).
   - *Controls that are found.*
     - The known spinor optimum `delta_2 = 0.349149` in dimension 2 is a local
       attractor: perturbations up to size 0.5 return to it within `3e-5`, at
       `n = 2, 6, 12`.
     - In dimension 12 with spinor spectra, all 4 of 4 random starts reach 0.34916.
   - *Balanced, n = 12.* 2 of 6 starts reach `0.63605`, and 1 more reaches 0.931.
     In a second batch with other seeds, 0 of 5 starts go below 1.016.
   - *Balanced, n = 24: blind.* The planted direct sum of two witnesses has
     `D = 0.636045`. Monotone polish from perturbations of this planted point
     gives:

     | perturbation size | final D |
     |---|---|
     | 0.05 | 0.636076 |
     | 0.1 | 0.6646 |
     | 0.2 | 0.6824 |
     | 0.4 | 0.6880 |

     So there are nearby critical points strictly above the planted value, and
     the descent does not return. The 8 random starts with basin hopping end at
     `1.0139` to `1.2325`.
   - *Spinor spectra, n = 6 and 24: blind for an identified reason.* The spinor
     curve (`A ~ {i,-i}`, `B ~ {w,w^2}` in `U(2)`) has a second critical point
     at `t = 2.28158` with `D = 1.31263`, where `r_1 = 1` exactly. At `n = 6` and
     `n = 24`, every random start converges to direct sums of copies of this
     spurious point. The analysis finds commutant dimension 3 and blocks
     `[2,2,2]` at `n = 6`, whereas the true value is `0.349149`.

## Consequences and scope

- The balanced sector reaches `0.636` in dimension 12. That is far below the
  defects of the exact representations of the `Delta(4,3,5)` quotient seen on
  the bus, which are about 0.96. A falsifiable decomposition of the target is
  therefore:
  - either `delta_bal` stays bounded below along `n = 12k`;
  - or some `n = 12k` beats 0.636.

  The census gives no evidence either way at `n >= 24`, because the method is
  demonstrably blind there (item 3). Any claimed numerical value of
  `lim delta_bal(n)` from fixed-spectrum local search at `n >= 24` should be
  discounted unless the search first recovers the planted double
  witness at `0.636`.
- The witness is not near-central (`gamma = 1.376`). So the "golden" bound
  `(sqrt 5 - 1)/2 = 0.618` for pairs with `A^2` nearly central (posted on the bus)
  does not apply to it. The witness sits `0.018` above that number.
- The statement says nothing about non-balanced sectors. It also says nothing
  about whether `delta_bal(n) -> 0`, which is what `T` being MF would require.
