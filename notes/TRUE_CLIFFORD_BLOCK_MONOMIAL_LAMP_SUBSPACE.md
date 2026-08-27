# Block-monomial Clifford models must diagonalize a lamp subspace

The collapse theorem of `TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md` does not
extend verbatim from abelian lamps to Clifford lamps, and the obstruction to
extending it is a single computable invariant. What does extend is a forced
structural feature: any block-monomial model of the Clifford cover carries a
**nonzero `G`-invariant `𝔽₂`-subspace of lamp words whose image is diagonal**.

That is a usable acceptance test on candidate Clifford models, and it explains
exactly why the abelian argument was free of this issue.

## Setting

Let `Γ ≤ G` be the Kun–Thom Theorem E pair, `X = G/Γ`. The **Clifford lamp
group** `C(X)` (`notes/NOTEPAD.md` ~20385) has generators `z`, `a_x` (`x ∈ X`)
and relations

    z² = 1,   [z, a_x] = 1,   a_x² = 1,   [a_x, a_y] = z  (x ≠ y),

so `C(X)/⟨z⟩ ≅ ⊕_X C₂` and `H_Cl = C(X) ⋊ G` is a central `ℤ/2` extension of
the Kun–Thom wreath `W = (⊕_X C₂) ⋊ G`.

Retain the block-monomial vocabulary of the companion note: `B` is
block-monomial over `Y` when `B(e_y ⊗ ξ) = e_{σ(y)} ⊗ V(y)ξ`, and
`π(B) := σ` is its permutation part, a group homomorphism
`U(m) ≀ Sym(Y) → Sym(Y)`.

**Definition.** A *block-monomial Clifford model* is a trace-preserving
embedding `Θ : L(H_Cl) → ∏_𝒰 M_{d_n}`, `d_n = |Y_n|·m_n`, with `Θ(z) = −1` and
with every `Θ(a_x)` and every `Θ(u_g)` represented by matrices block-monomial
over `Y_n`.

The hypothesis `Θ(z) = −1` is the faithful Clifford case; `Θ(z) = +1` collapses
the model to the abelian one, already covered by the companion note. Note the
lamps are **not** required to be diagonal — they cannot be, since they generate
a Clifford algebra, which is a factor. Only monomiality is asked, which under
Jordan–Wigner is what Majoranas actually satisfy.

## What survives, and what does not

**Lemma 1 is indifferent to abelianness.** The estimate
`‖A − B‖₂² ≥ 2·d_H(π(A), π(B))`, uniform in `m`, is a statement about
block-monomial matrices; nothing in its proof uses that the lamps commute.
Hence multiplicativity of `Θ` descends to permutation parts and

    ϖ := π ∘ Θ : H_Cl ⟶ 𝒮_𝒰

is a group homomorphism into the permutation ultraproduct. Since `Θ(z) = −1` is
a scalar, hence diagonal, `ϖ(z) = 1`, so `ϖ` factors through
`H_Cl/⟨z⟩ = W`:

    σ_W : W ⟶ 𝒮_𝒰.

So far this is exactly the abelian argument, and it is the reason one expects
the theorem to extend.

**Faithfulness on the lamps is no longer free.** This is the whole difference.
In the abelian case the lamps lie *in* the coarse diagonal, so their permutation
parts are trivial and `Θ̃` restricted to them is `Θ` itself — faithful and
trace-preserving for nothing. Here the lamps have nontrivial permutation parts,
and `π` can kill lamp words. Put

    𝒮 := { S ⊆ X finite : ∏_{x∈S} Θ(a_x) is diagonal }.

Then `𝒮 = ker(σ_W) ∩ (⊕_X C₂)` under the identification of finite subsets of
`X` with `⊕_X 𝔽₂`, and the abelian argument needs `𝒮 = 0`.

**`𝒮` is a `G`-invariant subspace.** It contains `∅`; it is closed under
symmetric difference because `(∏_S)(∏_T) = z^ε ∏_{SΔT}` with `z ↦ −1` scalar,
and a product of diagonals is diagonal; and it is `G`-invariant because
`Θ(u_g)` is block-monomial, so conjugation by it carries diagonals to diagonals
and permutes the lamps according to `g`. So `𝒮` is a `G`-submodule of the
permutation module `𝔽₂[X] = ⊕_{G/Γ} 𝔽₂`.

## Theorem

**Theorem.** Every block-monomial Clifford model has `𝒮 ≠ 0`.

*Proof.* Suppose `𝒮 = 0`. The acting group `G` is residually finite (Kun–Thom
Theorem E), hence LEF, hence sofic, so it has a sofic representation
`ρ : G → 𝒮_𝒰'`. Consider

    Ψ := σ_W ⊗ (ρ ∘ pr) : W ⟶ 𝒮_𝒰 × 𝒮_𝒰' ⊆ 𝒮_𝒰'',

a homomorphism into a permutation ultraproduct (product of finite sets). Its
kernel is `ker(σ_W) ∩ ker(ρ ∘ pr)`. An element of `ker(ρ ∘ pr)` has trivial
`G`-part, hence lies in the lamp group `⊕_X C₂`, so
`ker Ψ = ker(σ_W) ∩ (⊕_X C₂) = 𝒮 = 0`. Thus `Ψ` is injective, `W` embeds into
a metric ultraproduct of symmetric groups in the Hamming metric, and `W` is
sofic. That contradicts Kun–Thom Theorem A at the Theorem E pair. ∎

The step from "embeds into `𝒮_𝒰`" to "sofic" is the standard equivalence; in
this repository it is `Sofic/SoficUltraproduct.lean` together with the
separation-constant amplification of `Sofic/SoficAmplification.lean`, whose own
docstring records that the constant in `IsSofic` is not a convention.

## The hypothesis is not vacuous — Jordan–Wigner violates it

Take `k` qubits and the standard Jordan–Wigner Majoranas

    γ_{2j−1} = Z^{⊗(j−1)} ⊗ X ⊗ 1,   γ_{2j} = Z^{⊗(j−1)} ⊗ Y ⊗ 1.

Every one of these is monomial. But `X` and `Y` both have permutation part the
flip of bit `j`, while `Z` is diagonal with trivial permutation part. Hence

    π(γ_{2j−1}) = π(γ_{2j}) = flip_j,   π(γ_{2j−1} γ_{2j}) = 1,

even though `γ_{2j−1}γ_{2j} = ±i Z_j` is not central. So the permutation-part
map identifies the two Majoranas at each Jordan–Wigner site and kills their
product: `𝒮 ≠ 0` for the standard model, by construction rather than by
accident. This is precisely why the collapse theorem cannot be quoted at the
Clifford lane, and it is a genuine feature of Majoranas rather than an artefact
of a bad choice — any Jordan–Wigner ordering pairs sites.

## Consequence for the Clifford lane

The theorem is a constraint, not a refutation, and it is sharper than it looks
because the submodule structure is restricted.

`𝒮` is a nonzero `G`-submodule of `𝔽₂[G/Γ]` and `G` acts transitively, so if
`𝒮` contains a singleton it contains all of them and equals `𝔽₂[G/Γ]` — in
which case `σ_W` kills every lamp and the permutation part retains no lamp
information whatsoever. At the other end, `notes/PERFECT_CORE_KUN_THOM_WREATH.md`
Theorem 1 shows `[A, G] = I_X`, the augmentation kernel, for `G` perfect acting
transitively, so `I_X` is the natural proper candidate; if `𝒮 ⊇ I_X` then
`σ_W` factors through `(A/I_X) ⋊ G ≅ C₂ × G`, again retaining essentially no
lamp information.

So a block-monomial Clifford model must route a `G`-invariant subspace of its
lamp words into the diagonal, and the two structurally available choices both
make the induced permutation model lamp-blind. That is the same shape as
`Criterion/FiniteQuotientBlindness.compressedImage_eq`, which forces the image
of `Γ` to be normal in every finite quotient and thereby collapses the lamps to
`G/⟨⟨Γ⟩⟩`. Whether the coincidence of shape is more than a coincidence is not
settled here.

**Acceptance test.** For any proposed block-monomial Clifford model, compute
`𝒮` and check that it is a proper nonzero `G`-submodule. If `𝒮 = 0` the model
does not exist, by the theorem. If `𝒮` is everything, the model may exist but
its permutation part is useless, so whatever hyperlinearity it witnesses is
carried entirely by the fiber unitaries — and the question of what those can do
is `fiber-masa-free-cocycle` again, one level up.

## References

- `notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md` — the abelian theorem and
  Lemma 1.
- G. Kun and A. Thom, arXiv:2608.06222v1, Theorems A and E; verbatim in
  `research/artifacts/kun-thom-2608-06222-verified.md`.
- `notes/NOTEPAD.md` ~20385 for `C(X)` and the central-quotient identification;
  `notes/PERFECT_CORE_KUN_THOM_WREATH.md` Theorem 1 for `[A,G] = I_X`.
- `GroupApproximation/Sofic/SoficUltraproduct.lean`,
  `GroupApproximation/Sofic/SoficAmplification.lean`,
  `GroupApproximation/Sofic/LEFSofic.lean`.
