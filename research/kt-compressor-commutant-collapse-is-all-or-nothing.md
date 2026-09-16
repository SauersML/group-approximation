---
rg: 2
id: kt-compressor-commutant-collapse-is-all-or-nothing
kind: claim
title: For the Kun--Thom pair, commutant collapse under one strict compressor forces collapse under all, and one Laurent root decides it
distinct_from:
  relative-wall-commutant-growth: that proves, for every infranormal pair, that a wall for SOME compressor exists iff the Gamma-commutant is not Ad pi(G)-invariant (all compressors versus normalization); this proves, only for the Theorem E pair, that collapse for ONE strict monomial compressor already forces normalization, that one non-polynomial root decides it, and that in a wall the stabilizer in SL_d(Z) is exactly A_d.
  approximate-collapse-for-kt-compressor: that asks whether (CCR) holds for trace-faithful matrix-ultraproduct models; this is an exact, trace-free equivalence valid for every homomorphism into every group, and it proves nothing about which alternative occurs.
  kt-centralizer-normalization-hs: that asks whether normalization holds and records one-compressor (CCR) as a formally weaker kernel; this shows that at the Theorem E pair the kernel and normalization coincide model by model, for monomial compressors.
  rigid-compression-defect-normalization-dichotomy: that is a class-level equivalence between normalization and trivial rigid defects over all infranormal Kazhdan pairs; this is a per-model rigidity statement internal to the Theorem E pair, and it uses no approximation class and no property (T).
artifacts:
  - research/artifacts/kt-commutant-all-or-nothing-2026-09-16.md
---

**Setting.** Let `q` be a prime power and `r,d>=3`. Put `R_+=F_q[x_1,...,x_d]`,
`R=F_q[x_1^(+-1),...,x_d^(+-1)]`, `E=EL_r(R)`, `Gamma=EL_r(R_+)`, and
`G=E semidirect SL_d(Z)`. Here `L e_ij(f) L^(-1)=e_ij(beta_L f)` with
`beta_L(x^n)=x^(Ln)`. `SL_d(N)` denotes `SL_d(Z)` intersected with the
nonnegative integer matrices, and `A_d` the even permutation matrices.
`P_Gamma={g in G : g Gamma g^(-1) <= Gamma}` is the set of compressors.

Let `U` be **any** group and `pi : G -> U` any homomorphism. Put
`C_0=C_U(pi(Gamma))`. For `U=U(M)`, `M` a von Neumann algebra, `C_0` is the
unitary group of the relative commutant `pi(Gamma)' cap M`. Every element of a
von Neumann algebra is a linear combination of unitaries, so each condition
below may equivalently be read with `C_0` replaced by `pi(Gamma)' cap M`. No
trace, no injectivity and no property (T) is used.

**Theorem.** The following are equivalent.

1. `C_U(pi(t Gamma t^(-1)))=C_0` for **one** `t in SL_d(N) \ A_d`.
2. `C_U(pi(g Gamma g^(-1)))=C_0` for **every** compressor `g in P_Gamma`.
3. `pi(G)` normalizes `C_0`.
4. `C_0=C_U(pi(E))`.
5. `pi(e_12(f))` commutes with `C_0` for **one** `f in R \ R_+`. For
   example `f=x_1^(-1)`. Equivalently, `C_U(pi(Gamma_1))=C_0` for
   `Gamma_1=EL_r(F_q[x_1^(+-1),x_2,...,x_d])`.
6. Some `L in SL_d(Z) \ A_d` has `pi(L)` normalizing `C_0`.
7. `{L in SL_d(Z) : pi(L) normalizes C_0}` has finite index in `SL_d(Z)`.
8. For one `m in Z^d \ {0}`, `pi(diag(x^m,x^(-m),1,...,1))` normalizes `C_0`
   (an `r x r` diagonal matrix, which lies in `E`).

**Wall alternative.** If the conditions fail, which is exactly when a relative
wall exists for some compressor, the failure is total and rigid.

- `C_U(pi(L Gamma L^(-1)))` strictly contains `C_0` for **every**
  `L in SL_d(N) \ A_d`.
- The stabilizer `{L in SL_d(Z) : Ad pi(L)(C_0)=C_0}` equals `A_d`.
- For every `k != l` and every `f in R \ R_+`, `pi(e_kl(f))` fails to
  commute with `C_0`.
- The saturation `Gamma^sat={g in G : pi(g) commutes with C_0}` meets every
  root group in exactly its polynomial part: `Gamma^sat cap U_kl(R)=U_kl(R_+)`.

**Engine.** `Gamma^sat` is a subgroup with `C_0=C_U(pi(Gamma^sat))`, and its
normalizer is the stabilizer of `C_0`. The additive group
`S={f : e_12(f) in Gamma^sat}` is a subring between `R_+` and `R`, and it is
stable under every compressor substitution `beta_L`, `L in SL_d(N)`. Every such
subring is `R_+` or `R`; this is the subring dichotomy lemma of the route.

**Consequences for the (AC) wall.**

- The exact per-model commutant statement (CCR)_t, which the approximate
  question `approximate-collapse-for-kt-compressor` is designed to supply,
  does not depend on which strict monomial compressor `t` is used. This says
  nothing about the approximate (AC) formulation itself, which still mentions
  `t`.
- Per model, one-compressor (CCR) and full normalization are equivalent. So
  for the Theorem E pair the kernel in `kt-centralizer-normalization-hs` is
  not weaker than normalization.
- An enemy is exactly one element of `sigma(Gamma)' cap M` that fails to
  commute with the single unitary `sigma(e_12(x_1^(-1)))`.
- In an enemy model no element of `SL_d(Z)` outside `A_d` preserves the
  commutant.

The torus reduction recorded in the target is a different criterion.

*Remark, cited and not part of the theorem proved below.* Both alternatives
occur for some target group. Genuine finite-dimensional
unitary models satisfy (1) by linear dimension (`commutant-no-growth`), hence
all eight conditions. Per `kun-thom-clifford-cover-weakly-sofic` (with the
normal form `relative-wall-commutant-growth`), the Clifford cover realizes a
wall in a metric ultraproduct of finite groups.

DERIVATION
kt-compressor-commutant-collapse-all-or-nothing-proof
