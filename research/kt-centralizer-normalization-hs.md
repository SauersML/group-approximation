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

**2026-08-18b ((CCR) on the canonical congruence representation).**
A residual chain gives the canonical faithful-trace sofic
`σ = ∏_𝒰 (regular rep of G/N_n)` (`tr σ(g) = lim tr → 0` for
`g ≠ e`).  Three facts localize (CCR) there:

1. In congruence quotients the compression COLLAPSES:
   `π(tΓt⁻¹) = π(t)π(Γ)π(t)⁻¹ = π(Γ)` exactly, because the elementary
   part `E` is normal in `Q_M` and `π(Γ) = E` — the same
   finite-quotient-blindness that drives the two-point refutation.  So
   the coordinatewise commutants of `Λ̄_n` and `Γ̄_n` are EQUAL at every
   level and coordinatewise (CCR) is a triviality.

2. Hence the entire content of (CCR) for this `σ` lives in the
   **excess commutant** — elements almost-commuting with `σ(Λ)`
   elementwise without coordinate centralizer structure — precisely
   the approximate-vs-genuine homomorphism gap of Alekseev–Thom
   OP 6.2, now with a sharp question attached to it rather than a
   description problem.

3. The naive counterexample template dies structurally: taking
   `x = σ(t) y σ(t)⁻¹` with `y` in the coordinate commutant of
   `Γ̄` gives `[x, σ(γ₀)] = σ(t)[y, σ(t⁻¹γ₀t)]σ(t)⁻¹`, and
   `t⁻¹γ₀t ∈ E` by normality of `E` in `G`, so `y` commutes with it
   and `x` commutes with `σ(γ₀)` — the transported commutant never
   leaves the protected zone.  Any refutation of (CCR)-for-this-`σ`
   must build `x` with no coordinate structure at all; any proof must
   convert Kazhdan `(T)`-stability (almost-commuting with the
   generators of `Λ` ⟹ near the exact centralizer, uniformly in `n`)
   into control of exactly that excess.

Net: for the canonical `σ`, (CCR) is a clean, self-contained question
about excess commutants of Kazhdan images in sofic ultraproducts.

**2026-08-18e: the coarse slice is clean, and the enemy now has a
name.**  Decompose `L²(M) = L²(L(G)) ⊕ H` as `Ad G`-representations
(`L(G)` is conjugation-invariant).  The `L(G)`-slice is closed by
2026-08-18d.  Inside `H`: any sub-bimodule isomorphic to a multiple of
the coarse bimodule contributes NO `Λ`-fixed vectors — the conjugation
action on `ℓ²(G×G)`, `g·(a,b) = (ga, bg⁻¹)`, is free, and `ℓ²`
functions constant on infinite orbits vanish.  And since `Λ` has (T),
weak containment of `triv_Λ` upgrades to actual containment, so a
counterexample to (CCR) must be an HONEST `Λ`-spherical,
non-`G`-trivial sub-bimodule of `H` for a matrix ultraproduct `M` —
quasi-regular-shaped (`ℓ²(Γ/Λ)`-type) bimodule content actually
embedded, not just weakly approximated.  The same (T) fact helps the
refutation side too: to refute (CCR) it suffices to produce
almost-`Λ`-central elements of `M ⊖ L(G)` that are uniformly far from
`Γ`-central — (T) then converts them to an exact `Λ`-fixed,
non-`Γ`-fixed vector.  Both attack surfaces are now stated in
bimodule language; the question "which `L(G)`-bimodules are
matrix-ultraproduct-realizable with actual (not weak) spherical
content" is the precise residue.

**2026-08-18d: the group-algebra slice is PROVED, for every σ.**
`FC_Λ(G) = Z` (finite-orbit pigeonhole + transvection rigidity over
the compressed subring, which retains the constants), hence
`σ(Λ)' ∩ L(G) = σ(Γ)' ∩ L(G) = Z(L(G))` unconditionally — every
group-algebra-supported counterexample channel (centralizer excess,
finite-orbit sums) is dead.  See `ccr-group-algebra-slice(-proof)`.
The full question now lives entirely in `M ⊖ L(G)`.

**2026-08-18c: the canonical case is PROVED.**  (CCR) holds for every
coordinatewise ultraproduct of genuine finite-dimensional
representations with image collapse `π_n(Γ) ⊆ π_n(Λ)` — in particular
for the canonical congruence `σ` — by per-coordinate Kazhdan
uniformity (ε-commutation with the generators of `Λ` is `2ε/κ`-
commutation with EVERY element of `π_n(Λ)`, uniformly) composed with
the collapse.  See `ccr-for-coordinate-collapsing-models(-proof)`.
No groupoids, medians, or atomic invariants appear.  Consequences:
congruence models can never refute the route, and the open remainder
of THIS node is exactly the transport of that uniformity across the
approximate-coordinate gap (the OP 6.2 locus) for arbitrary `σ`.
