# Block-monomial fiber models collapse to permutation models

A hyperlinear model of the Kun–Thom wreath candidate cannot hide the coordinate
action in a growing unitary fiber. If the lamps sit in a coarse diagonal and
the group unitaries are block-monomial with respect to it, the permutation
parts alone already witness soficity of the generalized Bernoulli action, which
Kun–Thom Corollary D forbids.

This closes the most natural reading of "the trace is blind to sizes". The
trace is indeed blind to the fiber, but the fiber is not where the obstruction
lives: the obstruction is carried by the lamps, and the lamps are faithfully
represented on the coordinates whatever the fiber does.

## Setting

Fix the wreath candidate of Kun–Thom Theorem E: `q` a prime power, `r,d ≥ 3`,
`R₊ = 𝔽_q[x₁,…,x_d]`, `R = 𝔽_q[x₁^{±1},…,x_d^{±1}]` with `SL_d(ℤ)` acting by
monomial substitutions, `Γ = EL_r(R₊)`, `G = EL_r(R) ⋊ SL_d(ℤ)`, and

    W = (⊕_{G/Γ} ℤ/2ℤ) ⋊ G,    A = ⊕_{G/Γ} ℤ/2ℤ,
    M_KT = L(W) = L^∞(X) ⋊ G,   X = {±1}^{G/Γ},

with `a_x ∈ U(L^∞(X))` the lamp at the coset `x ∈ G/Γ` (the `x`-th coordinate
sign) and `u_g` the canonical unitaries. Write `τ` for the canonical trace,
`‖·‖₂` for the normalized Hilbert–Schmidt norm, and `𝒰` for a fixed free
ultrafilter.

For finite sets `Y` and integers `m ≥ 1` put `ℂ^{Y×[m]} = ℂ^Y ⊗ ℂ^m`. Call
`B ∈ U(Y × [m])` **block-monomial over `Y`** if there are `σ ∈ Sym(Y)` and
`V(y) ∈ U(m)` with

    B (e_y ⊗ ξ) = e_{σ(y)} ⊗ V(y)ξ                              (1)

for all `y ∈ Y`, `ξ ∈ ℂ^m`; `σ =: π(B)` is the **permutation part**. The
block-monomial matrices form a group `U(m) ≀ Sym(Y)`, and `π` is a group
homomorphism onto `Sym(Y)`, since composing (1) twice composes the
permutations.

**Definition.** A *block-monomial fiber model* of `M_KT` is a trace-preserving
`∗`-embedding

    Θ : M_KT ⟶ ∏_{n→𝒰} M_{d_n}(ℂ),    d_n = |Y_n| · m_n,

together with finite sets `Y_n` and integers `m_n ≥ 1`, such that under the
identification `ℂ^{d_n} = ℂ^{Y_n} ⊗ ℂ^{m_n}`:

- **(a)** `Θ(a_x) ∈ ∏_𝒰 (D_{Y_n} ⊗ 1)` for every `x ∈ G/Γ`;
- **(b)** every `Θ(u_g)` is represented by a sequence of matrices that are
  block-monomial over `Y_n`.

The fiber dimension `m_n` is unconstrained; `m_n → ∞` is the interesting case
and is what makes (b) strictly weaker than requiring permutation matrices.

## The rigidity lemma

**Lemma 1.** Let `A, B` be block-monomial over `Y` with permutation parts
`π, π'`. Then

    ‖A − B‖₂² ≥ 2 · d_H(π, π'),                                (2)

where `‖·‖₂` is normalized on `M_{|Y|m}` and `d_H` is the normalized Hamming
distance on `Sym(Y)`.

*Proof.* Fix `y` with `π(y) ≠ π'(y)`. By (1) the `y`-column block of `A` is
supported in the rows `{π(y)} × [m]` and that of `B` in the rows
`{π'(y)} × [m]`; those row sets are disjoint. Both blocks are unitary, so each
has squared Frobenius norm `m`, and the `y`-column block therefore contributes

    Σ_{i,j} |A_{(·,i),(y,j)} − B_{(·,i),(y,j)}|² = m + m = 2m

to the unnormalized sum. There are `d_H(π,π')·|Y|` such `y`, and every term is
nonnegative, so the unnormalized sum is at least `2m·d_H(π,π')·|Y|`. Dividing
by `d = |Y|m` gives (2). ∎

Lemma 1 is the exact point at which the fiber fails to help: it is a *lower*
bound on the Hilbert–Schmidt distance in terms of a datum the fiber cannot
touch, and it is uniform in `m`. Enlarging the fiber dilutes the trace of a
block, but it does not dilute a mismatch of permutation parts, because a
mismatch moves a whole block.

## The collapse

**Theorem 2.** No block-monomial fiber model of `M_KT` exists.

*Proof.* Suppose `Θ` is one, with representing block-monomials `B_n(g)` for
`Θ(u_g)` and permutation parts `σ_n(g) = π(B_n(g))`.

*Step 1: the permutation parts form a homomorphism.* Since `π` is a
homomorphism on `U(m_n) ≀ Sym(Y_n)`, the matrix `B_n(g)B_n(h)` is
block-monomial with permutation part `σ_n(g)σ_n(h)`, and `B_n(gh)` is
block-monomial with permutation part `σ_n(gh)`. As `Θ` is multiplicative in the
ultraproduct, `lim_𝒰 ‖B_n(gh) − B_n(g)B_n(h)‖₂ = 0`, so Lemma 1 gives
`lim_𝒰 d_H(σ_n(gh), σ_n(g)σ_n(h)) = 0`. Hence

    σ : G ⟶ 𝒮_𝒰 := ∏_{n→𝒰} (Sym(Y_n), d_H),   σ(g) := (σ_n(g))_𝒰,

is a group homomorphism into the permutation ultraproduct.

*Step 2: the lamps are covariant for `σ`.* Conjugation of `e_y e_y^* ⊗ 1` by a
block-monomial with permutation part `σ` yields `e_{σ(y)}e_{σ(y)}^* ⊗ 1`, the
fiber blocks cancelling; so conjugation by `B_n(g)` acts on `D_{Y_n} ⊗ 1`
exactly by the permutation `σ_n(g)`, with no error term. Identifying
`∏_𝒰(D_{Y_n} ⊗ 1)` with the diagonal ultraproduct `D_𝒰` on the `Y_n`, and
writing `θ := Θ|_{L^∞(X)}`, which lands in `D_𝒰` by (a), the relation
`u_g a_x u_g^* = a_{gx}` in `W` transports to

    σ(g) θ(a_x) σ(g)^* = θ(a_{gx})   for all g ∈ G, x ∈ G/Γ.    (3)

Since the `a_x` generate `L^∞(X)` as a von Neumann algebra and `θ` is normal,
(3) holds for all of `L^∞(X)`: `(θ, σ)` is a covariant pair for
`G ↷ L^∞(X)` in `∏_𝒰 M_{|Y_n|}`, with `θ` trace-preserving and faithful
(it is the restriction of the embedding `Θ`).

*Step 3: repair faithfulness on `G` by tensoring.* The pair `(θ, σ)` induces a
`∗`-homomorphism on the algebraic crossed product, but `σ` need not be
faithful — this is exactly what the fiber was supposed to buy, since
`τ(Θ(u_g))` involves the blocks and is unrelated to the fixed-point fraction of
`σ_n(g)`. It is bought back for free. The group `G` is residually finite
(Kun–Thom Theorem E), hence LEF, hence sofic, so it admits a sofic
representation: finite sets `Z_n` and maps `ρ_n : G → Sym(Z_n)` with
`lim_𝒰 d_H(ρ_n(gh), ρ_n(g)ρ_n(h)) = 0` for all `g,h` and
`lim_𝒰 |Fix ρ_n(g)|/|Z_n| = 0` for every `g ≠ 1`.

Put `Y'_n := Y_n × Z_n`, and define

    θ'(a) := θ(a) ⊗ 1,    σ'_n(g) := σ_n(g) × ρ_n(g).

Then `θ'` still lands in the diagonal on `Y'_n`, `σ'` is still a homomorphism
into `𝒮_𝒰`, and (3) still holds, so `(θ', σ')` is again a covariant pair. Let
`Φ : L^∞(X) ⋊ G → ∏_𝒰 M_{|Y'_n|}` be the induced `∗`-homomorphism.

*Step 4: `Φ` is trace-preserving, hence an embedding.* Both traces vanish off
the identity coset, so it suffices to check `τ(Φ(a u_g)) = τ(a u_g)` for
`a ∈ L^∞(X)` and `g ∈ G`. The matrix `Φ(a u_g) = (θ(a) ⊗ 1)(P_{σ_n(g)} ⊗ P_{ρ_n(g)})`
has `((y,z),(y,z))` entry equal to `θ(a)_y` when `σ_n(g)y = y` and
`ρ_n(g)z = z`, and `0` otherwise. Hence

    τ(Φ(a u_g)) = ( 1/|Y_n| · Σ_{y ∈ Fix σ_n(g)} θ(a)_y ) · ( |Fix ρ_n(g)| / |Z_n| ).

For `g = 1` both factors degenerate correctly and the value is
`τ(θ(a)) = τ(a)`. For `g ≠ 1` the first factor is bounded by `‖a‖` and the
second tends to `0` along `𝒰`, so `τ(Φ(a u_g)) = 0 = τ(a u_g)`. Thus `Φ` is
trace-preserving on the algebraic crossed product, extends normally to
`L^∞(X) ⋊ G`, and is injective, a trace-preserving `∗`-homomorphism out of a
von Neumann algebra with faithful normal trace being injective.

*Step 5: contradiction.* `Φ` is a trace-preserving embedding of
`L^∞(X) ⋊ G` into `∏_𝒰 M_{|Y'_n|}` with `Φ(L^∞(X)) ⊆ D_𝒰` and every `Φ(u_g)`
a permutation matrix. That is precisely a sofic action in the sense of
Păunescu Definition 1.4, which is the notion Kun–Thom use. So the generalized
Bernoulli action `G ↷ {±1}^{G/Γ}` is sofic — contradicting Kun–Thom
Corollary D, whose hypotheses hold at the Theorem E pair. ∎

## What Theorem 2 does and does not say

It says: a hyperlinear model of `W` may not preserve any *coarse block
decomposition* whose blocks carry the lamps. This is strictly stronger than
the corresponding statement for a full diagonal masa. A companion result
elsewhere in this corpus shows that approximate normalizers of the **full**
diagonal masa are close to monomials, and observes that the argument is sharp
in that hypothesis, since the Fourier-block unitary `⊕_j F_{m}` centralizes a
coarse block-constant subalgebra while sitting at distance `√2` from every
monomial. Theorem 2 shows that this sharpness does not open a door: a
Fourier-block unitary is still block-monomial over the coarse index set, its
permutation part is still well defined and still multiplicative, and the lamps
still ride on the coarse coordinates. Distance from monomials was never the
relevant measurement.

It does not say `M_KT` is not Connes-embeddable, and it must not be read that
way. Step 1 uses block-monomiality **exactly**, in the ultraproduct. A model
whose group unitaries are merely *approximately* block-monomial, with a defect
that does not vanish, is untouched — and that is the generic situation for the
decomposition into atoms of a finite window of the lamp algebra, where the
boundary of the window in `G/Γ` carries a constant fraction of the mass
(property (T), infinite index, no Følner sets) and one mismatched coordinate
costs a configuration-space defect of order one. The amplification obstruction
and Theorem 2 are therefore complementary rather than overlapping: Theorem 2
kills exact block structure, amplification kills the naive approximate one, and
what remains open is a model with no coarse block structure at all.

## Consequence for the flexible branch

The requirement on any hyperlinear model of the Kun–Thom wreath candidate is
now: the image of the lamp algebra must admit **no invariant coarse block
decomposition** — no tensor splitting `ℂ^{d_n} ≅ ℂ^{Y_n} ⊗ ℂ^{m_n}` with the
lamps in `D_{Y_n} ⊗ 1` and the group unitaries block-monomial over `Y_n`. Since
the lamp algebra is diffuse abelian and can always be conjugated into the
diagonal, and since a finite window of it has `2^k` atoms of equal trace, such
a decomposition is always present approximately; the content of the requirement
is that the approximation defect must stay bounded away from zero uniformly,
for every window and every splitting. That is a positive, checkable, and as far
as this corpus records unattempted specification, and it replaces the vaguer
"embed the Bernoulli algebra non-Cartanly".

## References

- G. Kun and A. Thom, *Nonsofic wreath products of residually finite groups*,
  arXiv:2608.06222v1, Theorem A, Corollary D, Theorem E. Verbatim statements
  and provenance in `research/artifacts/kun-thom-2608-06222-verified.md`.
- L. Păunescu, *On sofic actions and equivalence relations*, arXiv:1002.0605,
  Definition 1.4 and Notation 1.2.
- `GroupApproximation/Sofic/LEFSofic.lean` (`isSofic_of_isLEF`) and
  `GroupApproximation/Sofic/SoficUltraproduct.lean` for the sofic
  representation used in Step 3.
- `notes/OBSTRUCTIONS.md` §3 (amplification) for the complementary bound
  discussed above.
