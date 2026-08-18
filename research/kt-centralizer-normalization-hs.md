---
rg: 2
id: kt-centralizer-normalization-hs
kind: claim
title: Hilbert–Schmidt analogue of Kun–Thom centralizer normalization
invalidates: [growing-fiber-models]
distinct_from:
  invariant-cartan-completion: that asks for an invariant diagonal masa and routes through Corollary D; this asks for normalization of a relative commutant and routes through Theorem A's endgame — no masa appears in it at all
  hs-expander-block-decomposition: that is the HS transcription of Kun's decomposition, which is the INPUT to Kun–Thom Theorem 4.1; this is the transcription of Theorem 4.1 itself, and it needs the cluster groupoid and the two median arguments on top of any decomposition
artifacts:
  - docs/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

Let `Γ < G` be an infranormal, non-normal Kazhdan pair and let
`σ : G → U(∏_𝒰 M_(d_n))` be a trace-preserving (hyperlinear) representation.
Is the relative commutant `σ(Γ)' ∩ ∏_𝒰 M_(d_n)` normalized by `σ(G)`?

This is Kun–Thom Theorem 4.1 with `𝒮_𝒰` replaced by the unitary group of the
tracial ultraproduct. **A positive answer refutes hyperlinearity of `W`**, by
transcribing their proof of Theorem A verbatim: `Γ` fixes the coset `Γ`, so
`ρ(a_Γ)` lies in the relative commutant; normalization puts every
`ρ(a_(gΓ)) = ρ(g)ρ(a_Γ)ρ(g)⁻¹` there too; but for a strict compressor `t` and
`γ ∈ Γ \ tΓt⁻¹` one has `σ(γ)ρ(a_(tΓ))σ(γ)⁻¹ = ρ(a_(γtΓ)) ≠ ρ(a_(tΓ))`, the
two lamps being at `‖·‖₂`-distance `√2`.

## Why it is not a corollary of the permutation version

Kun–Thom's proof of Theorem 4.1 runs on the finite cluster groupoid of almost
equivariant partial bijections between the `Γ`-expander components: two median
arguments, one on the **vertex mass** of a connected groupoid component and one
on the **order of its isotropy group**, force a transported functor to be full.
Both invariants are counting invariants of a permutation action on a point set.
In the Hilbert–Schmidt category:

- property (T) still supplies the analogue of expansion for free — an action of
  a Kazhdan group on a tracial von Neumann algebra has a spectral gap on
  `L²(M) ⊖ L²(M^Γ)` — so the *expansion* input is not the obstacle;
- what is missing is the *component structure*. Kun–Thom's Lemma 2.3 identifies
  `D_𝒰^(σ(Γ))` with `∏_𝒰 D(Q_n)`, an **atomic** partition algebra whose cells
  have sizes. The fixed algebra `σ(Γ)' ∩ ∏_𝒰 M_(d_n)` of a hyperlinear
  approximation need not be atomic — for `σ ⊗ 1` it contains a `II₁` factor —
  so there are no component sizes and no isotropy orders to run medians on.

This is the decisive open sub-claim on the rigidity side. It is *a priori*
independent of `invariant-cartan-completion`: that one goes through Corollary D
and an invariant masa, this one through Theorem A and a relative commutant, and
neither is known to imply the other. Both, if established, refute
`hyperlinear-wreath-model`; both, if refuted, are consistent with either answer
to Q3.4.

`hs-expander-block-decomposition` is the natural first input — it is the HS
transcription of Kun's decomposition, which is what Kun–Thom feed into
Theorem 4.1 — but it is not recorded as a `requires` here, because even with a
decomposition in hand the two median arguments have no evident HS form: the
quantities they compare are a component's vertex mass and its isotropy order,
and neither survives when the blocks are matrix corners rather than orbits.

## Position relative to Alekseev–Thom Open Problem 6.2

Open Problem 6.2 of arXiv:2608.05362 — statement checked against the full text
in `docs/CREDIT_AND_PRIORITY_AUDIT.md` — asks whether the commutant of a
Kazhdan representation into a tracial matrix ultraproduct is an ultraproduct of
finite-dimensional subalgebras, i.e. whether it admits a **coordinate
description** by centralizers of lifts. This claim asks a different question
about the same object: not how the commutant is described, but whether it is
**normalized** by the ambient group.

The two are adjacent and the dependence runs one way. A positive answer to
OP 6.2 would supply, in the Hilbert–Schmidt category, exactly the coordinate
structure that Kun–Thom's proof consumes — components with masses and isotropy
groups on which medians can be run — and would therefore be the natural first
input here. A negative answer would say the coordinate picture fails already at
the description stage, which is where the flexible side expects the room to be.
Nothing here resolves OP 6.2, and this node must not be read as a claim on it:
OP 6.2 is a published open problem of Alekseev and Thom, and the repository's
interest is the downstream invariance question.

The same adjacency holds one metric class over. In any metric ultraproduct of
finite groups the ultraproduct commutant strictly contains the ultraproduct of
the coordinate centralizers, because the coordinate maps are approximate rather
than genuine homomorphisms; so OP 6.2's difficulty is present in the
bi-invariant category too and is not an artefact of unitaries.

Adjacent, and worth reading before attacking: Alekseev–Thom arXiv:2608.05362,
whose conclusion is that the centralizer of a sofic embedding of a Kazhdan
group is itself a metric ultraproduct of **permutation** groups. The
permutation-specificity of that conclusion is exactly the point at issue here.

## Attempts

**2026-08-18 (sharpening, no resolution).**  Two reductions that shrink
what must be proved, recorded after re-reading the endgame:

1. **The minimal sufficient kernel is one containment for one
   compressor.**  Unwinding `σ(g)(σ(Γ)' ∩ M)σ(g)* = σ(gΓg⁻¹)' ∩ M`, the
   Theorem-A endgame does not consume full `σ(G)`-normalization: the
   contradiction only needs `ρ(a_{tΓ}) ∈ σ(Γ)'`, i.e.

   ```text
   (CCR)   σ(tΓt⁻¹)' ∩ M  ⊆  σ(Γ)' ∩ M
   ```

   for ONE strict compressor `t` and every trace-preserving
   `σ : G → U(M)`, `M` a matrix ultraproduct.  The reverse containment
   is free from `tΓt⁻¹ ⊆ Γ`.  Slogan: *compressing the Kazhdan group
   must not grow its relative commutant.*  This is strictly weaker than
   the normalization question in the header (which quantifies over all
   `g`, including the incomparable `SL_d(ℤ)`-twisted copies), so a
   proof may attack (CCR) directly; a refutation of (CCR) kills the
   route while a refutation of full normalization would not.

2. **Amplification cannot refute it.**  The `σ ⊗ 1` example above
   breaks only the atomic *proof technique*, not the *statement*:
   `(σ ⊗ 1)(Γ)' ∩ (M ⊗ M_k) = (σ(Γ)' ∩ M) ⊗ M_k` and conjugation by
   `σ(g) ⊗ 1` acts componentwise, so normalization (and (CCR)) for
   `σ ⊗ 1` is equivalent to that for `σ`.  Any genuine counterexample
   must entangle the multiplicity space with the group image — plain
   multiplicity is invisible to the question.

Status after both: the hole is unchanged in kind — (CCR) is a new
rigidity statement with no known proof mechanism once atomicity is
gone — but its surface is smaller and better named than "transcribe
Theorem 4.1".  Adjacent recorded fact pointing the same direction:
`t ∈ Γ*` is REFUTED for KT pairs (the compressor lies outside the
profinite-closure skeleton), so (CCR) cannot be reached through
finite-quotient approximations of `t`; whatever proves it must use the
ultraproduct structure itself.
