---
rg: 2
id: clifford-diagonal-lamp-subspace
kind: claim
title: Block-monomial Clifford models must diagonalize a nonzero invariant lamp subspace
distinct_from:
  block-monomial-coordinate-collapse: that is the abelian case and is a non-existence result; this is the Clifford case, where the analogous model is NOT refuted but is forced to carry a nonzero invariant subspace of diagonal lamp words
  finite-quotient-blindness: that is about exact finite quotients of the group and normality of Γ's image; this is about which lamp words a block-monomial matrix model sends into the diagonal, with no finite quotient in sight
  compressed-commutant-majorana: that is a constructive target asking for one involution in a relative commutant; this is a constraint every block-monomial Clifford model must satisfy
artifacts:
  - notes/TRUE_CLIFFORD_BLOCK_MONOMIAL_LAMP_SUBSPACE.md
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
---

Let `H_Cl = C(X) ⋊ G` be the Clifford cover of the Kun–Thom wreath,
`X = G/Γ`. Call `Θ : L(H_Cl) → ∏_𝒰 M_{d_n}` a *block-monomial Clifford model*
if `d_n = |Y_n|·m_n`, `Θ(z) = −1`, and every `Θ(a_x)` and `Θ(u_g)` is
block-monomial over `Y_n`. Put

    𝒮 = { S ⊆ X finite : ∏_{x∈S} Θ(a_x) is diagonal } ⊆ ⊕_{G/Γ} 𝔽₂.

Then `𝒮` is a `G`-submodule of `𝔽₂[G/Γ]`, and **`𝒮 ≠ 0`**.

## Answer to the cross-lane question

cairn-wall asked whether `block-monomial-coordinate-collapse` extends from
abelian lamps in a coarse diagonal to Clifford lamps. Half of it does, and the
half that fails is the informative one.

What survives is the machinery: Lemma 1 of the companion note
(`‖A − B‖₂² ≥ 2 d_H(π(A),π(B))`, uniform in the fiber dimension) never uses
that the lamps commute, so permutation parts still form a homomorphism, and
since `Θ(z) = −1` is scalar it factors through `H_Cl/⟨z⟩ = W`. Wall's guess
that "the site action is recoverable from the permutation" is right that far.

What fails is faithfulness on the lamps, which in the abelian case was free
because the lamps *were* diagonal and their permutation parts were trivial.
Clifford lamps are monomial with nontrivial permutation parts, and the
permutation-part map can kill lamp words — so there is no pair of separated
lamps left to derive a contradiction from. The theorem above is what remains:
if `𝒮` were `0`, tensoring with a sofic representation of `G` would embed `W`
into a permutation ultraproduct and make it sofic, contradicting Kun–Thom
Theorem A.

**The hypothesis is violated by the standard model, not by a bad choice.**
Under Jordan–Wigner, `γ_{2j−1} = Z^{⊗(j−1)} ⊗ X` and `γ_{2j} = Z^{⊗(j−1)} ⊗ Y`
have the *same* permutation part — the flip of bit `j` — because `X` and `Y`
are both monomial with that flip while `Z` is diagonal. So
`π(γ_{2j−1}γ_{2j}) = 1` although `γ_{2j−1}γ_{2j} = ±i Z_j` is not central. Every
Jordan–Wigner ordering pairs sites, so `𝒮 ≠ 0` there by construction. This is a
feature of Majoranas.

## Why the constraint has teeth

`G` acts transitively on `X`, so if `𝒮` contains a singleton it is everything
and the permutation part retains no lamp information at all. At the other end
`notes/PERFECT_CORE_KUN_THOM_WREATH.md` Theorem 1 gives `[A,G] = I_X`, so the
augmentation kernel is the natural proper candidate; if `𝒮 ⊇ I_X` then the
induced map factors through `(A/I_X) ⋊ G ≅ C₂ × G` and is again lamp-blind.
Both structurally available options make the permutation part useless, which
means any hyperlinearity such a model witnesses is carried entirely by the
fiber unitaries — returning the question to `fiber-masa-free-cocycle` one level
up.

The shape is the same as `finite-quotient-blindness`, which forces `Γ`'s image
normal in every finite quotient and collapses the lamps to `G/⟨⟨Γ⟩⟩`. Whether
that is more than a coincidence of shape is not settled here and is not
asserted.

## Acceptance test

For any proposed block-monomial Clifford model, compute `𝒮`. If `𝒮 = 0` the
model does not exist. If `𝒮` is everything, the model may exist but proves
nothing through its permutation part. Recorded for
`compressed-commutant-majorana` and `kun-thom-clifford-crossed-product-ce`,
whose lane this constrains.
