---
rg: 2
id: qd-coefficient-models-miss-quotientless-kazhdan-kernels
kind: claim
title: Covariant models with quasidiagonal or nuclear coefficient algebra are trivial on every quotientless Kazhdan kernel, so Pimsner--Brown AF-embedding routes cannot build MF models of witness mapping tori
distinct_from:
  kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups: that is the single-group statement for quasidiagonal targets; this transfers it to normal subgroups of mapping tori and covariant pairs, adds the nuclear-in-corona case through Choi--Effros lifting, and records which mapping-torus construction classes it kills.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that kills stably finite certificates on the non-MF side (proofs of Rad_MF = K); this kills the opposite side, the quasidiagonal and AF crossed-product constructions of MF models nontrivial on K.
  kazhdan-regular-block-periodizations-of-mapping-tori-are-finite: that kills block-monomial periodizations with small wrap defect; this kills every model whose restriction to K lands in a quasidiagonal or nuclear coefficient algebra, whatever the wrap.
  brown-af-automorphism-crossed-product-equivalence: that is Brown's theorem, which gives AF-embeddings of A rtimes Z for AF A; this shows the theorem never applies to a quotientless Kazhdan kernel, because the kernel already dies inside A.
---

**ESTABLISHED** via `qd-coefficient-models-miss-quotientless-kazhdan-kernels-proof`.

**Theorem.** Let `K` be a group with property (T) and no nontrivial finite quotient. Let `H` be
any group containing `K`, for instance `H = K ⋊_ψ Z`. Let `Π : H → U(Q)` be a homomorphism into
the unitary group of a unital C*-algebra `Q`, and put `B = C*(Π(K))`. Then `Π|_K` is trivial in
each of the following cases.

- **(QD)** `B` is contained in a quasidiagonal C*-subalgebra of `Q`. Examples: an AF, RFD or
  quasidiagonal coefficient algebra, or `Q = ∏_n M_{k_n}(C)` itself.
- **(NUC)** `Q = ∏_n M_{k_n}(C) / ⊕_n M_{k_n}(C)` is a norm corona and `B` is contained in a
  separable nuclear C*-subalgebra of `Q`.

**Covariant form.** Let `ψ ∈ Aut(K)`, let `A` be a unital C*-algebra with `β ∈ Aut(A)`, and let
`ι : K → U(A)` be a homomorphism with `β ∘ ι = Ad(w) ∘ ι ∘ ψ` for some `w ∈ U(A)`. If `A` is
quasidiagonal, then `ι` is trivial. This holds in particular for AF `A`, and it does not depend on
`β`, on the crossed product `A ⋊_β Z`, or on its traces or `K_0`.

## Construction classes killed

The named invariant is the quasidiagonality (or nuclearity) of the coefficient algebra
`C*(Π(K))`. In every case the death step is the same: the restriction to `K` lands in a
quasidiagonal algebra, and it is trivial there by the Kazhdan projection argument of
`kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups`.

This applies to (XMF), to (EKL1), to (EK1) of `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`
and to `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`. In each, the kernel `K`
is Kazhdan with no finite quotient. Refuting any of them needs an MF model of `K ⋊_ψ Z` that is
nontrivial on `K`. The following classes cannot produce one.

1. **Pimsner--Voiculescu and Brown routes.** These embed `K` covariantly into an AF or quasidiagonal
   algebra `A`, then embed `A ⋊_β Z` into an AF algebra using
   `brown-af-automorphism-crossed-product-equivalence`. The criteria involved are stable
   finiteness, `H_β ∩ K_0(A)^+ = 0`, or a faithful `β`-invariant trace. The covariant form shows the
   route is empty: the model is already trivial on `K` inside `A`, before any crossed-product
   criterion is checked.
2. **Nuclear hosts inside the corona.** These realize the model inside a nuclear subalgebra of the
   corona: an AF-embeddable crossed product, a UCT algebra with a faithful trace in the sense of
   Tikuisis--White--Winter, a Cuntz--Pimsner or groupoid model with amenable data, or any
   separable nuclear algebra.
3. **Residually finite-dimensional and exact-product models.** These are models in
   `∏_n M_{k_n}(C)` before passing to the corona, or in RFD algebras. They are quasidiagonal, so
   case (QD) applies. This also re-proves the finite-dimensional case: honest finite-dimensional
   representations of `H` are trivial on `K`.

**Consequence for any nontrivial MF model.** Let `Π : K → U(∏ M_{k_n}/⊕ M_{k_n})` be nontrivial.
Then `C*(Π(K))` is MF, but it is not quasidiagonal, and it is not contained in any separable
nuclear subalgebra of the corona. This is the case, for instance, for the LEF models of
`EL_3(LC(X,F_q) ⋊ Z)`.

So every MF model of a witness mapping torus that is faithful on `K` is a covariant pair
`(C*(Π(K)), Ad Π(t))`. Its coefficient algebra is MF but neither quasidiagonal nor nuclear. The
constructions that survive build the implementing unitary directly in the corona over such a
coefficient algebra. The periodizations of Attempt 1 of `mf-kazhdan-quotientless-mapping-torus-exact-radical`
are of this kind. None of the operator-algebraic crossed-product permanence theorems applies to
them, since those theorems all assume quasidiagonal, AF or nuclear coefficients.

**Scope.** This is a class kill on the construction side only. It says nothing about whether (XMF)
or (EKL1) holds. It cannot certify `Rad_MF(G) = K` either, because it constrains models that are
nontrivial on `K` without excluding them.
