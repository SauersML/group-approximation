---
rg: 2
id: sylvester-near-minimal-leavitt-defects-are-multiplicative
kind: claim
title: Near-minimal Sylvester rank functions on the binary Leavitt unit group algebra have multiplicative disjoint-cylinder defects
distinct_from:
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that is near-minimal multiplicativity for rank-ultraproduct models, through kernel corners given by annihilator idempotents; this is the same statement for every Sylvester rank function, normalized by the augmentation quotient, with kernel corners built from stacks.
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w7-sylv-global`, route `sylvester-near-minimal-leavitt-defects-multiplicative-proof`;
artifact `research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md` Section 3;
verification requested from `w4-vf-linear-b`).

**Setting.** Let `R = L_(F_2)(1,2)` and `c_*^Syl = inf rho_omega(D_1000)` over non-augmentation Sylvester rank
functions `rho` on `F_2[R^x]`. It is at least `c_0 > 0` by `sylvester-leavitt-defect-gap-and-geometric-descent`.

**Statement.** Suppose `delta = rho_omega(D_1000) <= (1 + eps) c_*^Syl`. Let `A_1, ..., A_k` be pairwise disjoint
proper cylinders with proper union, and put `f(k) = rho_omega(D_(A_1) ... D_(A_k))`. Then
`|f(k+1) - delta f(k)| <= eps delta` and `|f(k) - delta^k| <= 2 eps delta`.

**At a minimizer** (artifact Corollary 3.5). If some non-augmentation `rho` exists, compactness makes the infimum
attained. At a minimizer:
- `f(k) = (c_*^Syl)^k` exactly;
- the range and kernel compressions at `D_(A_1) ... D_(A_k)` are again minimizers;
- the triangular count is an equality.

**Why it matters.** Add a Sylvester-form strict submultiplicativity bound
(`sylvester-disjoint-cylinder-defects-strictly-submultiplicative`). Then the computation of Consequence 3.2 of
`research/artifacts/rank-gate-axiom-audit-2026-09-12.md` excludes near-minimizers, so every Sylvester rank function
kills the two-root defect (route `sylvester-rank-triviality-via-strict-defect-submultiplicativity`). That uses no
regularity and no matrix approximation.

## Attempts

- 2026-09-12 `w5-regular-rankfn` (artifact Section 5.2). Two inputs of the regular proof (Proposition 4.1 of
  `research/artifacts/two-root-defect-descent-gap-2026-09-12.md`) are missing in class (A).
  - **Exact globality,** for the lower bound with constant `c_*^Syl`: `sylvester-leavitt-kazhdan-fixed-ideals-are-global`.
  - **A kernel corner.** The regular proof compresses to the right annihilator of the defect product. Sylvester
    rank functions compress to quotients by two-sided ideals and to images of commuting elements
    (`sylvester-rank-functions-descend-to-quotients-and-compressions`). A right annihilator of a non-central element
    is neither, and the triangular axiom only bounds the kernel part from above.
  - Regularity of every rank function (`sylvester-rank-functions-on-leavitt-units-are-regular`) would supply both.
- 2026-09-12 `w7-sylv-global` (artifact `sylvester-exact-globality-and-kernel-compression-2026-09-12.md`, Section 3).
  **Proved on paper.** Both missing inputs are now class (A). Write `P = D_(A_1) ... D_(A_k)` and `B = A_(k+1)`.
  - **Exact globality** (`sylvester-leavitt-kazhdan-fixed-ideals-are-global`, proved by submodularity). It makes the
    range compression `tau(A) = rho_omega(iota_B(A) P) / rho_omega(P)` fixed-point-free, so `f(k+1) >= c_*^Syl f(k)`.
  - **Kernel corner** (`sylvester-rank-functions-compress-to-commuting-kernels`).
    - `sigma(A) = (rho([P_n; A]) - n rho(P)) / (1 - rho(P))` is a rank function on the commuting subring.
    - Exact globality makes it fixed-point-free, so `rho_omega([P; D_(B1000)]) >= f(k) + c_*^Syl (1 - f(k))`.
    - The triangular count `rho([P; T]) + rho(PT) <= rho(P) + rho(T)` then gives
      `f(k+1) <= delta - c_*^Syl (1 - f(k))`.
  - **Statement corrected.** The tuples need proper union, for `V`-transitivity, as in the regular statement.
  - **Honest scope.** The claim holds for every Sylvester rank function, so it decides nothing alone.
    - The independent profile of the firewall models (`sofic-subgroups-carry-independent-cylinder-defects`, graphs of
      locally finite groups) has exactly the minimizer numbers above: multiplicative defects, equality in the
      triangular count, unchanged corners.
    - The first premise those models break is strict submultiplicativity itself.
