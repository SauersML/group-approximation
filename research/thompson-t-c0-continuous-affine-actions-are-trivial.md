---
rg: 2
id: thompson-t-c0-continuous-affine-actions-are-trivial
kind: claim
title: "Every affine isometric Hilbert action (and every cnd function) of Thompson's T or of its lift T-bar that is continuous for the uniform C^0 topology is trivial; hence no measurable Euler splitting over a space with C^0-continuous Koopman representation exists"
distinct_from:
  perfect-extension-splittings-are-not-uniformly-integrable: that kills splittings by integrability of beta (Hom(T-bar,R)=0) and spaces mapping equivariantly to S^1; this kills by a continuity hypothesis on the Koopman representation, with beta arbitrary measurable and X never mapping to S^1
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that bounds cocycles extracted from circle measures on the centre; this shows every C^0-continuous cocycle of T or T-bar is identically zero
  thompson-t-euler-class-splits-over-almost-invariant-space: that is the open existence statement (MT); this is one class-kill inside it, not a resolution
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that treats discrete witnesses X = T/H; those are C^0-discontinuous and untouched here
artifacts: []
---

**ESTABLISHED** by `thompson-t-c0-continuous-affine-actions-are-trivial-proof`.

**Setting.** `T ≤ Homeo+(S^1)`, and `T̄ ≤ Homeo~(S^1)` is its full preimage (periodic lifts to
`R`), with `z(x) = x + 1`. Both ambient groups carry the uniform (`C^0`, sup-metric) topology and
are Polish. `Γ` denotes `T` or `T̄`, with that subspace topology.

**Statement.**
- (A) Every unitary representation of `Γ` that is strongly continuous for the `C^0` topology is
  trivial.
- (B) Every affine isometric action of `Γ` on a real Hilbert space that is continuous for the
  `C^0` topology is trivial, i.e. `π = 1` and `b = 0`.
- (C) Every conditionally negative definite `ψ : Γ → [0,∞)` with `ψ(e) = 0` that is continuous
  at `e` for the `C^0` topology is identically `0`.
- (D) Kill for (MT). Let `(X, μ)` be a nonsingular `T`-space whose Koopman representation `κ` is
  `C^0`-continuous. Then `T` acts trivially a.e. and `κ = 1`, so hypothesis 3 of
  `central-extension-haagerup-from-measurable-euler-splitting` (a measurable `β` with
  `β(z, ·) = 1`) fails. By (A) it gives a homomorphism `T̄ → R` with `z ↦ 1`.
- (E) Sufficient condition for (D). `X` is Polish, the `T`-action extends to a jointly continuous
  `Homeo+(S^1)`-action, and `μ` is a `T`-invariant probability. Then `μ` is `Homeo+(S^1)`-invariant
  and `κ` is `C^0`-continuous.
  - Example: `X = Homeo+(S^1)/PSL2(Z)`, the space of Farey-type tessellations. It is the natural
    transplant of the Fuchsian witness in the calibration, and by (E)+(D) it carries no
    `T`-invariant probability at all.

**Named invariant.** Unitary triviality of `Homeo+(S^1)` and `Homeo~(S^1)`, pulled back along the
dense embedding `Γ ⊂ closure`.

**Death step.** `C^0`-continuity extends the representation to the closure. There it is trivial on
every point stabilizer, which is `≅ H+[0,1]` (Megrelishvili). Point-fixing elements generate the
group.

**Calibration (why the kill is not vacuous).**
- `Δ̃ = ⟨a,b,c | a² = b³ = c⁷ = abc⟩`, the preimage of the `(2,3,7)` triangle group in
  `PSL2(R)~`.
  - It is perfect: the abelianized relation matrix has determinant `−1`.
  - Its centre `⟨z⟩` is infinite cyclic and its Euler class is bounded, exactly as for `T̄`.
- Yet `Δ̃` has a pmp (MT)-witness.
  - Take a free non-cocompact lattice `Λ_0 < PSL2(R)`, a section `Λ_0' ≅ Λ_0` of its preimage
    (which exists because `Λ_0` is free), and `X = PSL2(R)/Λ_0`, of finite volume.
  - `PSL2(R)~/Λ_0' → X` is a principal `⟨z⟩`-bundle. A measurable trivialization gives
    `β : Δ̃ × X → Z` with `β(z, ·) = 1`.
  - `L²(X)` contains the constants, so the Koopman representation has almost invariant vectors.
  - `Δ(2,3,7)` is Haagerup.
- So perfectness plus a bounded Euler class do not forbid pmp witnesses. The obstruction for `T̄` is
  the non-local-compactness of its `C^0` closure: `PSL2(R)` has many continuous unitary
  representations, and `Homeo+(S^1)` has none.

**What survives.**
- Witnesses whose Koopman representation is `C^0`-discontinuous: dyadic, PL or breakpoint-sensitive
  structure (for example Farley-type cubical data, or `T/H` for discrete `H`).
- Merely quasi-invariant measures on circle-functorial spaces, where the Radon–Nikodym cocycle
  breaks `C^0`-continuity.

Sanity: `T` is Haagerup (Farley). So by (C), its proper cnd functions are necessarily
`C^0`-discontinuous, which is consistent.
