# Charges do not extend over the compressors, and the genuine shadow is rigid

Two results on the Kahl–Schneider lane, both proved here rather than cited.

The first settles, negatively, the question of whether an invariant charge
extends over the compressors where Connes embeddability does not: the generic
extension construction is induction, induction needs co-amenability, and
property (T) with infinite index forbids it. The hoped-for asymmetry between
Hahn–Banach and the amalgamated-free-product problem does not exist at that
level — and the charge side is in fact worse off, since its obstruction is a
theorem rather than an open problem.

The second removes a flagged gap. Bekka's characterization of amenable
representations of Kazhdan groups was recorded as unread (Springer paywall) and
therefore unusable. It is derivable from standard ingredients in half a page,
so it is derived, and the conclusion is the one that was feared: the entire
content of the Kahl–Schneider criterion for the wreath candidate sits in the
gap between *near* and *genuine*.

Throughout, `Γ ≤ G` is the Kun–Thom Theorem E pair, `X = G/Γ`,
`A = ⊕_X ℤ/2ℤ`, `W = A ⋊ G`, and `W₀ = (⊕_{X₀} C₂) ⋊ Γ` is the positive core
of `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md` with `X₀ = TΓ/Γ`, `T = ΓL₊`,
`L₊ = SL_d(ℤ) ∩ M_d(ℕ)`.

## 1. No invariant mean on the coset space

**Proposition 1.** Let `G` have property (T) and let `Γ ≤ G` have infinite
index. Then there is no `G`-invariant finitely additive probability measure on
`G/Γ`. Equivalently, `Γ` is not co-amenable in `G`.

*Proof.* Suppose `m` is a `G`-invariant mean on `ℓ^∞(G/Γ)`. Finitely supported
probability densities are weak-\* dense in the means, so there is a net
`(f_i)` of finitely supported probability densities on `G/Γ` with
`g·f_i − f_i → 0` weak-\* for each `g`. Weak-\* and norm closures of a convex
set of functionals agree (Hahn–Banach), so after passing to convex
combinations — Day's trick — we may assume `‖g·f_i − f_i‖₁ → 0` for every
`g ∈ G`.

Put `ξ_i = f_i^{1/2} ∈ ℓ²(G/Γ)`, a unit vector. The elementary inequality
`|√a − √b|² ≤ |a − b|` for `a, b ≥ 0` gives

    ‖g·ξ_i − ξ_i‖₂² ≤ ‖g·f_i − f_i‖₁ ⟶ 0,

so the quasi-regular representation `ℓ²(G/Γ)` has almost invariant unit
vectors. Property (T) then supplies a nonzero invariant vector. Since `G` acts
transitively on `G/Γ`, an invariant vector is a constant function, and a
nonzero constant lies in `ℓ²(G/Γ)` only when `G/Γ` is finite. ∎

This is the same fact `notes/OBSTRUCTIONS.md` §3 records as "`G ↷ G/Γ` has no
Følner sets (property (T), infinite index)", stated in the form the charge
language needs.

## 2. The positive core's charge does not induce

`positive-core-bernoulli-ce` gives an honest sofic action `Γ ↷ X₀`, hence by
Elek–Szabó's set-level criterion an essentially free amenable almost-action of
`W₀` — a set `Ω₀` carrying a `W₀`-invariant finitely additive probability
charge with `μ(Fix(w)) = 0` for `w ≠ 1`. The natural way to extend this to `W`
is induction.

**Proposition 2.** There is no `W`-invariant finitely additive probability
charge on the induced set `W ×_{W₀} Ω₀`.

*Proof.* The induced set fibres `W`-equivariantly over `W/W₀`, so a
`W`-invariant charge on it pushes forward to a `W`-invariant mean on `W/W₀`.
Under `W ↠ G` with kernel `A`, the image of `W₀` is `Γ`, so `W₀ ≤ A ⋊ Γ` and
there is a `W`-equivariant surjection

    W/W₀ ⟶ W/(A ⋊ Γ) ≅ G/Γ.

Pushing forward again gives a mean on `G/Γ` invariant under `W`, hence under
`G` since `W` acts through `G`. Proposition 1 forbids it. ∎

So the foothold does not extend by the generic construction, and it fails for
the same property (T) reason that everything else on this branch fails for.

**The asymmetry that was proposed does not exist.** The reason to prefer the
charge lane was that extending a finitely additive invariant measure is
Hahn–Banach's home ground, whereas extending Connes embeddability across an
amalgamated free product over a nonamenable base is a named open problem
(Gao–Junge). Proposition 2 shows the comparison was mis-drawn. Hahn–Banach
extends a charge from a subalgebra of sets to a larger one *with the same
invariance group*; it does not extend an invariant charge along a group
inclusion, and the object that has to be extended here is a charge for a group
that does not preserve the set it lives on. What is left of the charge lane is
exactly the non-induced constructions — that is, the *near* freedom, which is
the same freedom every other route on this branch is asking for.

Recorded so that induction is not attempted a second time: on this comparison
the charge side is strictly worse off than the algebra side, because
Proposition 1 is a theorem and Gao–Junge Problem 1 is open.

## 3. The genuine shadow is rigid

Bekka defines a unitary representation `π : G → U(H)` to be *amenable* when
there is a state `m` on `B(H)` with `m(π(g)Aπ(g)^*) = m(A)` for all `g ∈ G`,
`A ∈ B(H)`.

**Proposition 3.** Let `G` have property (T) and let `π` be an amenable unitary
representation of `G`. Then `π` has a nonzero finite-dimensional
subrepresentation.

*Proof.* Normal states are weak-\* dense in the state space of `B(H)`, and
`Ad π` preserves both. Starting from the invariant state `m` and applying
Day's trick exactly as in Proposition 1, there is a net of density operators
`ρ_i` with

    ‖π(g) ρ_i π(g)^* − ρ_i‖₁ ⟶ 0   for every g ∈ G.

The Powers–Størmer inequality `‖a^{1/2} − b^{1/2}‖₂² ≤ ‖a − b‖₁` for positive
`a, b`, applied with `a = π(g)ρ_iπ(g)^*` and `b = ρ_i` — note
`a^{1/2} = π(g)ρ_i^{1/2}π(g)^*` — gives

    ‖π(g) ρ_i^{1/2} π(g)^* − ρ_i^{1/2}‖₂² ⟶ 0.

Set `ξ_i = ρ_i^{1/2}`, a unit vector of the Hilbert–Schmidt space
`HS(H) ≅ H ⊗ H̄` carrying the unitary representation `Ad π`. So `Ad π` has
almost invariant unit vectors, and property (T) supplies a nonzero invariant
vector: a nonzero `T ∈ HS(H)` with `π(g)Tπ(g)^* = T`, i.e. `T ∈ π(G)'`.

Then `T^*T` is a nonzero positive trace-class operator in `π(G)'`. Trace-class
operators have discrete spectrum with finite multiplicities away from `0`, so
for small `λ > 0` the spectral projection `p = 1_{[λ,∞)}(T^*T)` is a nonzero
**finite-rank** projection, and `p ∈ π(G)'` because `T^*T` is. Hence `pH` is a
nonzero finite-dimensional `π(G)`-invariant subspace. ∎

This recovers what Bekka is reported to prove via the Hulanicki–Reiter theorem.
It is derived here rather than cited because the primary source was not
readable; the ingredients — density of normal states, Day's convexity trick,
Powers–Størmer, and the spectral theorem for trace-class operators — are all
standard, and none of them is specific to this problem.

## 4. Consequence for the Kahl–Schneider lane

Kahl–Schneider prove that a group is hyperlinear exactly when it admits an
essentially free amenable **near** representation. Suppose `π` were an
essentially free amenable **genuine** representation of `W`. Restricting the
invariant state to `G ≤ W` shows `π|_G` is amenable, and `G` has property (T)
by Kun–Thom Theorem E, so Proposition 3 gives a nonzero finite-dimensional
subrepresentation of `π|_G`. Finite-dimensionality is precisely the regime in
which this repository's rigidity results bite:
`Criterion/CommutantRigidity.commutant_no_growth` collapses the relative
commutant for genuine finite-dimensional representations, and
`Criterion/ExactCompression.fixedSubmodule_map_eq` supplies the invariant size
(`finrank`) that `no_strict_compression_of_invariantSize` needs.

So the genuine case is rigid, and the whole content of the criterion for `W`
lies in the gap between *near* and *genuine*. The charge lane is therefore
**not** independent of the rigidity branch in the way that was hoped: it is
independent exactly to the extent that flexibility is, and no more. That is a
real answer to the question rather than an obstruction — the lane is not dead,
but its softness is the softness of approximate representations, not a new
resource.

## References

- P. Kahl and F. M. Schneider, *Hyperlinearity via amenable near
  representations*, arXiv:2504.10988; statement verbatim in
  `research/hyperlinear-near-representation-criterion`.
- G. Elek and G. Szabó, arXiv:math/0408400, for the set-level criterion and the
  definition of an essentially free amenable action; verbatim in
  `research/artifacts/kun-thom-2608-06222-verified.md`.
- M. E. B. Bekka, *Amenable unitary representations of locally compact groups*,
  Invent. Math. 100 (1990) 383–401 — **not read**; Proposition 3 is proved
  above rather than quoted.
- `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md`, `notes/OBSTRUCTIONS.md` §1 and §3.
