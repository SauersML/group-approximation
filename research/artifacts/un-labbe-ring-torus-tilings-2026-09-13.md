# Torus quantum tilings decide exact matriciality of SFT crossed products; witnesses must grow

Lane `un-labbe-ring`, 2026-09-13. Status: two general results, ESTABLISHED (unreviewed). Row 7 of the UN
calibration table (the Labbé ring `LC(Ω_U, F_q) ⋊ Z^2`) is still UNDECIDED.

## 0. Target and outcome

Target: does `R = LC(Ω_U, F_q) ⋊ Z^2` embed unitally in an algebraic matrix ultraproduct (exactly matricial)?
By `matricial-z2-sft-crossed-products-give-quantum-tilings` this is the existence of covariant quantum tiling
families at every scale.

Outcome: undecided in both polarities. What is proved here:
- **Theorem 1 (torus form).** For a free minimal `Z^2`-SFT `Ω` and a finite field `k`, `R_(Ω,k)` is exactly
  matricial iff for every `D` some finite torus `Z^2/Λ` carries a nonzero finite-dimensional module of the
  translation-free torus tiling algebra `𝒯_(D,Λ)(Ω,k)`. Translation operators are recovered by induction.
- **Theorem 2 (growth).** For an infinite minimal `Z^2`-SFT, any witnesses at scales `D -> ∞` have dimensions
  `-> ∞`, and every period torus of a scale-`D` family has sup-diameter `> 2D`.

So no fixed dimension, fixed algebra or fixed torus can witness row 7, and the witnesses that matter live in
characteristic `p`.

## 1. Setting

`Ω ⊆ A^(Z^2)` is an SFT with forbidden patterns in `B_r = {h : |h| <= r}` (sup norm), `L_(B_D)(Ω)` its
`B_D`-language, `k` a field, `R_(Ω,k) = LC(Ω,k) ⋊ Z^2`. A *covariant `D`-family* on a finite-dimensional
`W != 0` consists of idempotents `E_a(z)` and commuting invertibles `U_1, U_2` with `E_a(z) = U^z E_a(0) U^(-z)`,
satisfying (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`. These are the finite-dimensional modules of
the local presentation `A_D(Ω,k)`.

**Torus tiling algebra.** For finite-index `Λ ≤ Z^2` put `T_Λ = Z^2/Λ`. `𝒯_(D,Λ)(Ω,k)` is the `k`-algebra on
generators `e_a(t)` (`a ∈ A`, `t ∈ T_Λ`) with relations:
- (T1) `sum_a e_a(t) = 1` and `e_a(t) e_b(t) = δ_ab e_a(t)`;
- (T2) `[e_a(t), e_b(t')] = 0` whenever `t' - t` has a representative in `B_(2D)`;
- (T3) `prod_(h ∈ B_D) e_(π(h))(t + h) = 0` for every `π ∉ L_(B_D)(Ω)`.
The factors in (T3) commute by (T2), since `B_D` has sup-diameter `2D`. The *sup-diameter* of `T_Λ` is
`max_t min { |w| : w ∈ t }`.

## 2. Theorem 1 (torus form)

**(a) Induction.** A nonzero finite-dimensional `𝒯_(D,Λ)`-module `V` induces a covariant `D`-family on
`W = ⊕_(s ∈ T_Λ) V`, with `U_1, U_2` of finite order.

**(b) Restriction.** A covariant `D`-family over a finite field restricts, with
`Λ = ker(Z^2 -> GL(W), g ↦ U^g)`, to a nonzero `𝒯_(D,Λ)`-module.

**(c) Specialization.** If `R_(Ω,k)` (`k` finite) embeds unitally in `∏_ω M_(d_n)(F_n)` for some fields `F_n`,
then for every `D` there is a covariant `D`-family over `k`.

**(d) Equivalence.** For `k` finite and `Ω` free minimal: `R_(Ω,k)` is exactly matricial iff for every `D` there
is `Λ` such that `𝒯_(D,Λ)(Ω,k)` has a nonzero finite-dimensional module.

*Proof of (a).* Put `(U^g ξ)_s = ξ_(s+g)`, and let `E_a(z)` act on the summand indexed by `s` as `e_a(z̄ + s)`,
where `z̄` is the class of `z`. Then `U^g E_a(0) U^(-g)` acts on summand `s` as `e_a(s + ḡ)`, which is how
`E_a(g)` acts there. So covariance holds, and `U_1, U_2` commute with finite order. On each summand (Q1) is
(T1). If `|z - z'| <= 2D`, then `(z̄ + s) - (z̄' + s)` has a representative in `B_(2D)`, so (T2) gives (Q2).
(Q3) at `z` is (T3) at `z̄ + s`. `W != 0`. ∎

*Proof of (b).* `U^λ = 1` for `λ ∈ Λ`, so `E_a(z + λ) = E_a(z)`, and `e_a(t) := E_a(z)` for `z ∈ t` is well
defined. (T1) is (Q1). If `t' - t` has a representative `w ∈ B_(2D)`, choose `z ∈ t` and `z' = z + w`; (Q2) gives
(T2). (T3) is (Q3). `U_i` has finite order because `GL(W)` is finite. ∎

*Proof of (c).* This is item 1 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid` (un-converse); the short
argument, for completeness. Fix `D`. The scale-`D` covariant identities are finitely many elements of `R`:
`sum_a χ_[a] = 1`, `χ_[a] χ_[b] = δ_ab χ_[a]`, `[u_w χ_[a] u_w^(-1), χ_[b]] = 0` for `w ∈ B_(2D)`,
`prod_(h ∈ B_D) u_h χ_[π(h)] u_h^(-1) = 0` for `π ∉ L_(B_D)(Ω)`, `u_(e_1) u_(e_2) = u_(e_2) u_(e_1)`, and
`u_(e_i) u_(e_i)^(-1) = 1`. For ω-most `n` the model is exact on them. The matrices `E_a(0)`, `U_i^(±1)` then
form an `F_n`-point of the affine variety over `F_p` cut out by these identities with `d = d_n`. It has
characteristic `p`, since the unital map kills `p`. A variety over `F_p` with a point over a field of
characteristic `p` has an `F̄_p`-point, hence a point over some `F_(p^m)` containing `k`. Restricting scalars to
`k` gives a covariant family over `k`. ∎

*Proof of (d).* (⇒) (c), then (b). (⇐) By (a), there are covariant families over `k` at every scale. The
families-to-matricial direction of `matricial-z2-sft-crossed-products-give-quantum-tilings` gives the embedding.
Its proof takes the colimit of the local presentations, and uses simplicity of `R_(Ω,k)` for free minimal `Ω`
together with `simple-rings-with-local-matrix-models-are-matricial`. ∎

## 3. Theorem 2 (growth)

Let `Ω` be an infinite minimal `Z^2`-SFT. Fields are arbitrary.

**(a) Periods.** If `D >= r` and a `Λ`-periodic family (`E_a(z + λ) = E_a(z)`) on a finite-dimensional
`W != 0` satisfies (Q1)–(Q3) at scale `D`, then `T_Λ` has sup-diameter `> 2D`.

**(b) Dimensions.** If `D_j -> ∞` and `V_j != 0` are finite-dimensional `A_(D_j)(Ω, k_j)`-modules, then
`dim V_j -> ∞`.

*Proof of (a).* If the sup-diameter is `<= 2D`, every difference of classes has a representative in `B_(2D)`.
So by periodicity and (Q2) all `E_a(z)` commute. Commuting idempotents on a finite-dimensional space have a
common eigenvector `v != 0`; put `x(z) =` the unique `a` with `E_a(z) v = v`. For each `z`, the product in (Q3)
for `π = x|_(z + B_D)` fixes `v`, so `x|_(z + B_D) ∈ L_(B_D)(Ω)`. Since `r <= D`, `x ∈ Ω`. But `x` is
`Λ`-periodic, and an infinite minimal system has no finite orbit. ∎

*Proof of (b).* For `m <= D_j` and `ρ : B_m -> A`, put `w_j(ρ) = rank(prod_(h ∈ B_m) E_(ρ(h))(h)) / dim V_j`.
The factors commute by (Q2). Then:
1. `w_j(ρ) ∈ (1/dim V_j) Z_(>=0)`;
2. `sum_ρ w_j(ρ) = 1`, and marginals are consistent, by (Q1) and commutation inside `B_(D_j)`;
3. `w_j` is translation-invariant, since ranks are invariant under conjugation by `U^z`;
4. `w_j(ρ) = 0` if `ρ ∉ L_(B_m)(Ω)`, because every extension of `ρ` to `B_(D_j)` is outside the language, (Q3)
   kills each, and their sum is the product for `ρ`.

Suppose `dim V_j <= N` along a subsequence. Pass, by a diagonal argument over the countably many `ρ`, to a
further subsequence with `w_j(ρ) -> w(ρ)` for all `ρ`. By 2–4 and Kolmogorov extension, `w` is a shift-invariant
Borel probability measure `μ` on `Ω`. `supp μ` is closed, invariant and nonempty, so it is `Ω` by minimality;
`μ` has no atoms, since an atom would force a finite orbit. Hence there is `ρ ∈ L(Ω)` with
`0 < μ([ρ]) < 1/N`: shrink cylinders around a point. Along the subsequence `w_j(ρ) -> μ([ρ])`, so eventually
`0 < w_j(ρ) < 1/N`, which contradicts item 1 with `dim V_j <= N`. ∎

**Remark.** `Ω_U` is strictly ergodic (`labbe-shift-is-a-toral-rotation-coding`, item 4). So for Labbé's shift
the rank vectors of any witnesses converge to the Haar-coded measure along the whole sequence, not only along
subsequences.

## 4. Consequences

- **Row 7, exact form.** Over `F_q`, `labbe-wang-shift-crossed-product-is-exactly-matricial` is equivalent to: for
  every `D` some torus tiling algebra `𝒯_(D,Λ)(Ω_U, F_q)` has a nonzero finite-dimensional module (Theorem 1(d);
  `Ω_U` is free minimal by `minimal-aperiodic-wang-shift-exists`).
- **Field precision.** `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale` asks for families over *some*
  field at each scale. That suffices for its payoff, non-finite-presentation, but not for row 7. Exact matricial
  models of the `F_q`-ring force families over finite fields of characteristic `p` (Theorem 1(c)); families in
  characteristic `0` concern a different ring.
- **Growth.** Any witnesses have unbounded dimension and unbounded period tori (Theorem 2). A bounded-dimension
  search can only give evidence at bounded scale.
- **Win-win recalled** (un-converse, `labbe-wang-shift-crossed-product-is-exactly-matricial`). "Yes" makes every
  `GL_n(R)` LEF and kills finite presentation. "No" gives the simple, finitely generated, stably finite,
  non-matricial ring that separates the two U3 converses.

## 5. Attempts and firewalls (not established)

- **Frequency counting.** At a fixed scale no obstruction, as un-converse recorded: rational invariant local
  weights exist. In the limit, ranks force dimension growth (Theorem 2(b)), which by itself contradicts nothing.
- **Quantum-torus smearing.** Clock–shift matrices approximate the rotation `x + φ^(-2) n`, but their position
  observables do not commute. So the atoms of `P_U` with slanted sides (directions `(1,-1)`, `(1,-φ)`) have only
  approximate spectral idempotents. (Q1)–(Q3) need exact identities; this yields rank-metric models of
  Ara–Claramunt type, not torus tilings. Not pursued.
- **Small searches.** Not run. Below the wall-rigidity scale `D_0` a hit may be a two-dimensional wall certificate
  rather than contextual, and by Theorem 2 bounded dimension cannot persist to large `D`. A meaningful search needs
  dimension `>= 3`, tori of sup-diameter `> 2D`, and `D >= D_0`, and `D_0` is not explicit.
- **What "no" must prove.** For some `D`, a certificate, uniform in `Λ`, that every `𝒯_(D,Λ)(Ω_U, F_q)` has no
  nonzero finite-dimensional module. Full quantum rigidity (`J_D = 0`, gate (a)) suffices but is stronger.
- **What "yes" must build.** Contextual torus tilings whose frames change around both cycles of `T_Λ`, with
  dimension growing in `D`. The context complex on a torus is not simply connected, so the tree-cover
  commutation of the gluing artifact (Proposition P2) does not apply.

## 6. Credit and bounds

- Definitions, local presentations and the fixed-field families-to-matricial direction come from
  `sft-crossed-product-fp-iff-quantum-rigid` and `matricial-z2-sft-crossed-products-give-quantum-tilings`.
  Specialization is item 1 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid`. All three are unreviewed.
- New here, own arguments, unreviewed: the translation-free torus algebra, the induction (Theorem 1(a)), the
  equivalence (d), and Theorem 2. No literature search beyond the graph.
