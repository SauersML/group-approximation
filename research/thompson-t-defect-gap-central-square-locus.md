---
rg: 2
id: thompson-t-defect-gap-central-square-locus
kind: claim
title: For exact Z/4 * Z/3 pairs, 7 D + 45 ||[A^2,B]|| >= 2/3, so T-defect is >= 1/7 on the SL(2,Z) locus [A^2,B] = 0; the two-dimensional minimum is delta_2 = 0.3491491..., a root of d^10 - 5d^8 + 5d^6 + 6d^4 - 9d^2 + 1, attained by an SU(2)-dense pair on that locus
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that reduces T not MF to inf_n delta_n > 0 and computes delta_1 = 2 sin(pi/12); this computes delta_2 exactly (strictly smaller than delta_1) and proves an explicit dimension-free lower bound on the neighbourhood of the locus where A^2 commutes with B.
  thompson-gap-witnesses-need-nonamenable-image: that proves D >= 1/2 on the virtually solvable-image locus; this gives a dimension-free bound on a locus defined by a commutator condition, which contains non-amenable (SU(2)-dense) images. It also exhibits an exact pair with D = 0.349 < 1/2, so the constant 1/2 there is not the global gap, even in dimension 2.
  thompson-t-has-full-mf-radical: that is the target, a uniform gap over all nontrivial pairs; this proves the gap only where ||[A^2,B]|| < 2/135, and shows that any MF witness must keep A^2 uniformly non-central.
  thompson-t-pentagon-winding-rigidity: that is a winding-number rigidity statement about r_P; this is a norm inequality that uses r_2 and r_P and never r_1, and it needs no winding number (kappa = 0 for the SU(2) minimiser).
artifacts:
  - experiments/thompson-t-defect-census-2026-09-17/census.py
  - experiments/thompson-t-defect-census-2026-09-17/dim2_exact.py
  - experiments/thompson-t-defect-census-2026-09-17/out_dim2_exact.json
  - experiments/thompson-t-defect-census-2026-09-17/dim2_lipschitz.py
  - experiments/thompson-t-defect-census-2026-09-17/out_dim2_lipschitz.json
  - experiments/thompson-t-defect-census-2026-09-17/verify_central_j.py
  - experiments/thompson-t-defect-census-2026-09-17/out_verify_central_j.json
  - experiments/thompson-t-defect-census-2026-09-17/lbfgs.py
  - experiments/thompson-t-defect-census-2026-09-17/exhaustive.py
  - experiments/thompson-t-defect-census-2026-09-17/out_exh_n3.jsonl
  - experiments/thompson-t-defect-census-2026-09-17/out_exh_n4.jsonl
  - experiments/thompson-t-defect-census-2026-09-17/locus.py
  - experiments/thompson-t-defect-census-2026-09-17/out_locus.jsonl
  - experiments/thompson-t-defect-census-2026-09-17/perturb_dsum.py
  - experiments/thompson-t-defect-census-2026-09-17/run_perturb.py
  - experiments/thompson-t-defect-census-2026-09-17/out_perturb_dsum.jsonl
  - experiments/thompson-t-defect-census-2026-09-17/homotopy.py
  - experiments/thompson-t-defect-census-2026-09-17/out_homotopy_control.jsonl
---

**ESTABLISHED** by `thompson-t-defect-gap-central-square-locus-proof` (written proof, with a
grid-plus-Lipschitz certificate for part (A)). Unreviewed. Not Lean-verified.

## Setting

This uses the notation of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`.
- An *exact pair* is `(A, B)` in `U(n)^2` with `A^4 = B^3 = 1`.
- Put `X = BAB`, `J = A^2`, `W = J B^2 J`, and
  `r_1 = [X, JXJ]`, `r_2 = [X, W X W^(-1)]`, `r_P = (BA)^5`, with `[x,y] = x y x^(-1) y^(-1)`.
- Norms are operator norms. Write `eps_i = ||r_i - 1||` and `D = max(eps_1, eps_2, eps_P)`.
- Put `gamma = ||J B - B J||`, the *non-centrality of the square*.
- `delta_n` is the minimum of `D` over nontrivial exact pairs in `U(n)`. `T` is not MF iff
  `inf_n delta_n > 0`.

## Statement

**(A) The exact value of `delta_2`.**

```text
delta_2 = 0.34914910598516613701...,   the root of  d^10 - 5 d^8 + 5 d^6 + 6 d^4 - 9 d^2 + 1  near 0.349.
```

- `delta_2 < delta_1 = 2 sin(pi/12) = 0.5176`.
- Up to conjugation, the minimiser is `A = diag(i, -i)` and `B = R(t) diag(w, w^2) R(t)^T`, with `R(t)` the
  rotation by `t = 0.1014860629688...` and `w = e^(2 pi i/3)`.
- At the minimiser `eps_1 = 0` and `eps_2 = eps_P = delta_2`.
- `x = tr(BA) = -1.6964948870...` is a root of the irreducible `x^5 - 5x^3 - x^2 + 5x + 1`.
- The minimiser lies on the locus `J = -1`, and its image is dense in `SU(2)`. In particular the image is
  not amenable.
- Every other two-dimensional profile has minimum `>= 0.516`.

**(B) Key inequality.** Every exact pair, in every dimension, satisfies

```text
|| B J - 1 ||  <=  5 eps_2 + 2 eps_P + 45 gamma.
```

**(C) Dimension-free gaps.** Let `(A, B)` be a nontrivial exact pair.
1. If `J = -1`, then `D >= 1/7`.
2. If `J = +1`, then `D >= sqrt(3)/7`.
3. If `gamma = 0`, then `D >= 1/7`. Here `gamma = 0` means that `A^2` is central in the image, that is,
   the pair is a representation of `G0 / <<[a^2, b]>> = Z/4 *_(Z/2) Z/6 = SL(2,Z)`, with `b' = a^2 b`.
4. In general, `7 D + 45 gamma >= 2/3`.

So on this locus the infimum lies in `[1/7, 0.3491]`, and the upper end is attained in dimension 2.

**(D) Consequence for MF witnesses.** Any exact pair with `D < 2/21` has

```text
|| [A^2, B] ||  >=  (2/3 - 7 D) / 45.
```

So a sequence of pairs witnessing that `T` is MF (`D -> 0`) must have `||[A^2, B]|| >= 2/135 - o(1)`. The
square of the order-4 generator must stay uniformly non-central.

## Why it matters, and what it does not do

- **Where the qualitative content comes from.** A qualitative version of (C) on the exact locus
  `gamma = 0` also follows by compactness. A sequence with `D -> 0` and `gamma -> 0` would give a
  homomorphism `T -> U_F` in which `alpha^2` is central. Because `T` is simple and non-abelian, that
  homomorphism is trivial, which contradicts spectral rigidity (L0c of the criterion proof). The new
  content is:
  - the explicit, dimension-free constants;
  - linear stability in `gamma`;
  - an argument that uses only `r_2` and `r_P` (never `r_1`);
  - the exact `delta_2`.
- **Where the argument dies.** It dies at the two steps that move `J` past `B`: step 2 (`r_2` against
  `[C,B]`) and step 4 (`(B^(-1) J)^5` against `B J`). Each move costs `gamma`, so the bound is empty once
  `gamma >= 2/135`. Any extension to the full target must control `[A^2, B]` from `r_1` and `r_2`
  directly. The dimension-2 minimiser, where `r_1 = 1` identically, shows that `r_1` alone does not
  force `gamma` to be small.
- **Correction of an easy belief.** The amenable-locus constant `1/2`, and `delta_1 = 0.5176`, are not
  the global gap. A non-amenable exact pair in `U(2)` already reaches `0.349`.

## Evidence on `delta_n` for `n >= 3` (numerical, not claimed)

- **n = 3.** Exhaustive fixed-profile L-BFGS (420 runs) found a best value of `0.349229`. This is
  consistent with `delta_3 = delta_2`, realised by `delta_2 (+)` a character.
- **Local rigidity.** Direct sums of the dimension-2 minimiser with characters, and two or three copies
  of it (`n <= 7`), were perturbed in the full unitary orbit of `B` (`out_perturb_dsum.jsonl`,
  126 runs). None went below `delta_2`.
- **n >= 4 is not informative. The planted control fails.** The profile `m = (0,2,0,2)`, `k = (0,2,2)`
  in `U(4)` contains `delta_2 (+) delta_2`, so its minimum is `<= 0.3492`. None of the following found
  it; every run ended at `0.5176` or higher:
  - the exhaustive `n = 4` census (825 runs);
  - the locus search on `A^2 = -1` for `n = 4, 5, 6` (1507 runs, stopped early);
  - 12 relator-homotopy runs.

  In `n = 2`, random starts find `delta_2` 4 times out of 10. So "no pair below `delta_2` found at
  `n >= 4`" is **not** evidence that `delta_n = delta_2`.

The conjecture `delta_n = delta_2` for all `n >= 2` is open and is not claimed here.
