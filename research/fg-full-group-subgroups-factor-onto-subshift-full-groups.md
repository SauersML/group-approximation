---
rg: 2
id: fg-full-group-subgroups-factor-onto-subshift-full-groups
kind: claim
title: A finitely generated subgroup of the full group of any Cantor action descends to the full group of a subshift factor, isomorphically when the subgroup is infinite simple
distinct_from:
  fp-subshift-full-group-subgroups-extend-to-sft: That extends a finitely presented subgroup of a free subshift's full group up to an SFT neighbourhood; this moves a finitely generated subgroup of an arbitrary, possibly non-expansive, Cantor system's full group down to a subshift factor, which need not be free.
  fp-alternating-full-groups-of-free-subshifts-force-sft: That forces a free subshift to be of finite type when its alternating full group is finitely presented; this is the reduction that brings non-expansive hosts into the symbolic setting where such results apply.
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

**ESTABLISHED** (direct proof: `fg-full-group-subgroups-subshift-factor-proof`). It has not
been independently reviewed, and no novelty is claimed: coding factors are standard.

**Setting.**
- A countable group `Λ` acts by homeomorphisms on a Cantor space `X`.
- `[[Λ ~ X]]` is the group of homeomorphisms `g` with a continuous cocycle `c_g`,
  `g(x) = c_g(x)·x`.
- For a finite clopen partition `P` of `X`, the coding map `π_P : X -> P^Λ` is
  `π_P(x)(μ) =` the cell of `P` containing `μ·x`.
- `Λ` acts on `P^Λ` by `(λ·z)(μ) = z(μλ)`, and `X_P = π_P(X)` is a subshift.

**Theorem.** Let `Γ = <g_1, ..., g_k> ≤ [[Λ ~ X]]`. Fix cocycles `c_i` of `g_i` and `c'_i` of
`g_i^{-1}`, and let `P` refine all their level sets.
1. **Descent.**
   - `π_P` is a continuous `Λ`-equivariant surjection.
   - There are `ḡ_i ∈ [[Λ ~ X_P]]` with `π_P ∘ g_i = ḡ_i ∘ π_P`.
   - `g_i -> ḡ_i` extends to a surjective homomorphism `θ_P : Γ -> Γ_P = <ḡ_1, ..., ḡ_k>`.
2. **Nontriviality.** Suppose `g_i` moves `x`, with `g_i(x) = c·x ≠ x`. If `P` also has a
   clopen set containing exactly one of `x` and `c·x`, then `ḡ_i ≠ e`. The same holds for
   every finer partition.
3. **Simple case.** If `Γ` is infinite and simple, then `θ_P` is an isomorphism for every such
   `P`. So `Γ` is isomorphic to a subgroup of `[[Λ ~ X_P]]` with `X_P` an infinite subshift.
   It is finitely presented if `Γ` is.
4. **Inherited dynamics.**
   - `X_P` is minimal whenever `X` is.
   - `(π_P)_* μ` is invariant, and of full support if `μ` is.
   - Stabilizers can only grow: `Stab(π_P x) ⊇ Stab(x)`.
5. **Abelian acting groups.**
   - Let `Λ` be abelian and `X` minimal. Then `Fix(λ)` is closed and invariant in `X_P`,
     so it is empty or everything.
   - With `K` the kernel of `Λ ~ X_P`, the quotient `Λ/K` acts freely, and `X_P` is a free
     minimal subshift over `Λ/K`. Its points are `K`-invariant colourings.
   - `Λ/K` is infinite when `Γ` is infinite simple, since `X_P` is infinite.
   - So every finitely generated infinite simple subgroup of the full group of a minimal
     Cantor `Λ`-system is isomorphic to a subgroup of the full group of a free minimal
     subshift over an infinite quotient of `Λ`.

**Consequences for `fp-infinite-simple-amenable-group`, case (S2).**
- **Non-expansive hosts add nothing.** A finitely presented infinite simple subgroup of the
  full group of any Cantor `Λ`-system is one of the full group of a subshift over the same
  `Λ`, with the same minimality and invariant measures.
- **Abelian acting groups.** Non-free and non-expansive minimal hosts reduce to free minimal
  subshifts over infinite quotients of `Λ`, which is case (S1).
- **What is left of (S2).** Subshifts over non-abelian `Λ` with nontrivial stabilizers, and
  non-minimal hosts. The artifact records where the free-subshift obstructions break there.
