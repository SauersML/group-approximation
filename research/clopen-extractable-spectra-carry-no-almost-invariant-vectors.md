---
rg: 2
id: clopen-extractable-spectra-carry-no-almost-invariant-vectors
kind: claim
title: "Class-kill for C(C,Z) ⋊ V: a spectral part carried by a V-invariant character set with an equivariant Borel map to probabilities on proper clopen sets has norm at most 1032 times the defect under h_1, h_2, h_3; so no central-growth witness is carried by countable sums of Haar extensions over nontrivial finite clopen algebras"
distinct_from:
  extractable-character-spectra-carry-no-almost-invariant-vectors: that needs an equivariant map to Prob(C); this needs one only to Prob(proper clopens), and no equivariant map Prob(proper clopens) -> Prob(C) exists (Stab_V(U) fixes no probability on C), so this does not follow by composition, and the Haar-extension class is not known to satisfy the hypothesis of that theorem; the new step is the leaf-Lebesgue averaging, which is equivariant for h_1, h_2, h_3 on deep clopens only
  cantor-integer-relative-t-witnesses-avoid-measure-characters: that section principle needs an equivariant section into finitely additive probabilities on the clopen algebra of C; this needs a section into probabilities on the countable set of proper clopens, and gives an explicit constant rather than a limit statement
  thompson-v-amenable-actions-are-free-off-fixed-points: that shows, for invariant means on discrete V-sets, that setwise clopen stabilizers are null (rigid covers); this transfers the corresponding non-amenability of V acting on proper clopens to spectral laws of C(C,Z) ⋊ V, with an explicit three-element constant, and applies it to Haar extensions
  thompson-v-finitary-structure-stabilizers-are-not-co-amenable: that concerns stabilizers of finitary structures over mean-free V-sets; this uses only clopen stabilizers and works on the dual of C(C,Z)
  cantor-integer-maps-central-direction-has-relative-t: that is the full open relative-(T) assertion; this kills one more class of witnesses for its negation and leaves infinite-cut characters open
  cantor-central-witnesses-have-long-range-dependence: that kills independent or mixing witness laws through the additivity invariant; the Haar extensions killed here are independent only below the cut, while the cut and the values on it may be coupled arbitrarily, so that kill does not cover them in general
artifacts:
  - research/clopen-extractable-spectra-no-almost-invariant-vectors-proof.md
---

**ESTABLISHED** by `clopen-extractable-spectra-no-almost-invariant-vectors-proof`.

**Setting.** As in `extractable-character-spectra-carry-no-almost-invariant-vectors`:
- `A = C(C,Z)` and `G = A ⋊ V`, with `h_1, h_2, h_3 ∈ V` the three prefix moves defined there.
- `𝒞` is the countable set of proper nonempty clopen subsets of `C`. `V` acts on it, and so on
  `Prob(𝒞)`.
- For a unitary representation `π` of `G`, `E` is the `A`-spectral measure on `Â`.

**Theorem L (V acts non-amenably on proper clopens, explicitly).** Let `η ∈ Prob(𝒞)`. If
`‖(h_i)_*η − η‖_TV ≤ ε` for `i = 1, 2, 3`, then `ε ≥ 1/516`.

**Theorem M (clopen-extraction kill).** Let `X ⊆ Â` be a `V`-invariant Borel set with a Borel map
`Φ : X → Prob(𝒞)` such that `Φ(vχ) = v_*Φ(χ)` for all `v ∈ V`. Let `ξ` be a unit vector with
`‖π(h_i)ξ − ξ‖ ≤ ε` for `i = 1, 2, 3`. Then `‖E(X)ξ‖ ≤ 1032 ε`.

**Clopen-extractable families.** Each of the following gives such a `Φ`, by taking the uniform law
on the listed finite set of proper nonempty clopens:
- a `V`-equivariant Borel map to finite clopen partitions with at least two pieces (its atoms);
- a map to nonconstant `f ∈ C(C,K)` for any set `K` (its nonempty level sets);
- a map to `A ∖ Z·1_C` (its nonempty level sets).

**Corollary (Haar extensions over finite cuts).** Let `B` be a finite Boolean algebra of clopens and
`A_B ≤ A` its step functions. For a character `χ` of `A_B`, let `μ_(B,χ)` be the Haar probability on
the coset `{χ' ∈ Â : χ'|A_B = χ}`. Let `Ω` be any countable set of pairs `(B, χ)` with `B ≠ {∅, C}`.
Then for every `π` and unit `ξ` as in Theorem M, the part of `ξ` whose spectral law is absolutely
continuous with respect to `Σ_(ω∈Ω) μ_ω` has norm at most `1032 ε`.

So no witness of central growth, of non-(T), or of Problem B(Z) is built from "a random finite cut,
Haar below it", whatever the law of the cut and of the values on the cut.

**Invariant and death step.**
- The invariant is the leaf partition: the set of maximal pure cylinders of a clopen. Here a cylinder
  is pure if it lies inside the clopen or misses it.
- Every member dies at the same step. Leaf-uniform Lebesgue averaging pushes the law on `𝒞` forward
  to a probability on `C` that is almost invariant under `h_1, h_2, h_3`. This works because shallow
  clopens have mass at most `46ε`, and on deep clopens the leaf map commutes with the three moves. The
  three-move paradox then applies.

**Not covered (survivors).**
- Characters from which no finite cut can be read off equivariantly. Examples are laws concentrated
  on characters whose natural cut is infinite: random open sets or perfect nowhere-dense closed sets
  with infinitely many leaves.
- There, leaf averaging has no normalizable equivariant weighting. Weights `λ(ℓ)^β` fail because
  `h_1` rescales one region by `1/2` and another by `2`.
- Haar measure on a fibre `χ(1_C) = θ` (trivial `B`) is `V`-invariant. It is not concentrated near
  the characters that are almost trivial on `1_[0]`, so it is not a witness.

**Relevance.**
- `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` (R1) implies Problem B(Z). That implies a
  `C_0` witness with no `1_C`-invariant vectors, and by Theorem M such a witness is asymptotically
  carried off every clopen-extractable set.
- So any positive construction for R1, `2V` or Problem B(Z) must live on characters whose finite
  structure cannot be read off equivariantly.
