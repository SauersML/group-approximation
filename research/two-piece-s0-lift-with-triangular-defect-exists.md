---
rg: 2
id: two-piece-s0-lift-with-triangular-defect-exists
kind: claim
title: Some two-piece lift of s0 through Thompson-type units has a vanishing off-diagonal defect
distinct_from:
  two-piece-s0-lifts-telescope-to-a-corner: that computes the product of every two-piece lift pair and says when it is a unit; this asserts that data with a vanishing off-diagonal piece exist, which is one sufficient case of that criterion
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that asks for any left-invertible lift of s0; this asks for a two-piece lift whose product with its partner is 1 plus a square-zero kernel element, a more specific shape
artifacts:
  - research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md
---

Let `A = F_2[R^x]` with `R = L_(F_2)(1,2)` and evaluation `pi`. There exist:
- an idempotent `E^` of `A` with `pi(E^) = s0t0`, with `E1^ = 1 - E^`;
- units `g1, g2` as in `two-piece-s0-lifts-telescope-to-a-corner`, with `h = g1^(-1) g2`;

such that

    E^ [h] E1^ = 0      or      E1^ [h^(-1)] E^ = 0.

By item 4 of `two-piece-s0-lifts-telescope-to-a-corner`, the lift pair `a, b` then has `b a` a unit. So `a`
witnesses `left-invertible-lift-of-s0-in-leavitt-group-algebra`.

## Attempts

**2026-09-12, swap-group idempotents and double cosets (lane `w3-kap-visible`).** Artifact Section 3.

* **Rigidity (Lemma 3.3).** If `b a` is a unit, and in particular in the triangular case,
  `F_2[<supp E^, h>]` is not directly finite. So `<supp E^, h>` is not sofic.
* **Exact test on a finite subgroup (Lemma 3.1).** Let `E^` lie in `F_2[F]` for a finite `F`, and put
  `D = F ∩ h F h^(-1)`. Then `E^[h]E1^ = 0` exactly when `E^ ⊗ E1^ = 0` in `F_2[F] ⊗_(F_2[D]) F_2[F]`, where `D`
  acts on the second factor through `h^(-1) D h`.
* **Dead: every swap-group lift, for every `h` (Proposition 3.6).** Take `E^` to be either idempotent lift of
  `s0t0` in `F_2[<1+s0t1, 1+s1t0>]`, that is `xy` or `P0^` of
  `binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap`. Neither piece vanishes, by cases on `D`:
  - `D = 1`: the tensor map is injective;
  - `D = C_2`: parity, since one of the two supports has three elements;
  - `D = C_3`: the `F_4` block carries `xy ⊗ yx != 0`;
  - `D = S_3`: equal dimensions would force `g1^(-1) P_01 g1 = P_1`.
* **Example (Computation 3.5).** The Thompson units `g1 : 0w->00w, 10w->01w, 11w->1w` and
  `g2 : 1w->01w, 00w->00w, 01w->1w` give `h : 1w->10w, 00w->0w, 01w->11w` and `D = 1`.
* **Never both at once.** For `E^` supported on a finite subgroup, both pieces cannot vanish together. That would
  nest `[h]E1^[h^(-1)]` strictly below `E1^`, which `nested-two-finite-subgroup-idempotents-have-strict-rank`
  forbids.
* **Where it dies.** A triangular witness needs two things:
  - `E^` supported off the swap group algebra, for example on the deeper constants `GL_(2^k)(F_2)` (artifact
    Remark 1.3) or with infinite support;
  - a unit `h` with `<supp E^, h>` non-sofic.

  No such candidate has been examined.

**2026-09-12, HNN transfer (lane `w4-kap-triangular`).** Artifact
`research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md`.

* **Dead: every finite-subgroup idempotent, every `h`** (`finite-support-triangular-two-piece-s0-lifts-do-not-exist`).
  - A vanishing piece says that a group element shifts a finite-subgroup idempotent right ideal into itself.
  - That equation lives on one double coset, so it also holds in the HNN extension of the support group along
    conjugation by `h`.
  - That extension is virtually free, so its group algebra is directly finite, and the shift must be an equality
    (`finite-subgroup-idempotent-ideals-admit-no-proper-group-shift`).
  - Evaluation refutes the equality.
  - This covers the constants `GL_(2^k)(F_2)` (including `GL_4(F_2)`), dyadic permutation constants, Klein constants
    and odd cyclic constants. It replaces the case split of Proposition 3.6.
* **General supports.** With `K = <supp E^>`, a triangular witness makes the group algebra of
  `HNN(K, K ∩ hKh^(-1))` not directly finite.
* **What survives.**
  - supports generating an infinite subgroup whose HNN extension has a non-directly-finite group algebra;
  - finite-subgroup idempotents conjugated by units of `A`: `h` becomes a unit, and the one-coset transfer fails;
  - non-triangular unit products;
  - lifts with three or more pieces whose zero pattern carries a cycle of nontrivial partial conjugations, recorded in
    `finite-support-multi-piece-triangular-s0-lift-exists`. Two pieces never carry such a cycle.
