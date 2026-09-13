# The measure side without towers: a simple Kazhdan group that is linear sofic and not LEF

Lane `un-sofic-not-lef`, 2026-09-13. Written proofs, UNREVIEWED.

**Question.** For a minimal effective ample groupoid with an invariant measure but no exact matricial models, what does the
rank-metric route give for `EL_N` over its Steinberg algebra: sofic, linear sofic over a finite field, or hyperlinear?

**Answer in one case that needs no tilings.**
- Take an amenable, finitely presented, non-residually-finite group `Γ`, a free minimal subflow `X` of `2^Γ`, and
  `R = LC(X, F_q) ⋊ Γ`.
- For every `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))` is infinite, finitely generated, simple and Kazhdan. It is
  `F_q`-linear sofic, and it is NOT LEF.
- The rank route gives linear soficity. The acting group, which sits inside `S_N`, blocks LEF.
- Soficity and hyperlinearity of `S_N` stay open (Section 5).

## 0. Setting and notation
- `Γ` is a countable group acting minimally by homeomorphisms on a compact totally disconnected metrizable space `X`, and
  `k` is a field.
- `A = LC(X, k)`, and `R = A ⋊ Γ` is the algebraic crossed product: finite sums `Σ f_g u_g` with
  `u_g u_h = u_(gh)` and `u_g f u_g^(-1) = g.f`, where `(g.f)(y) = f(g^(-1) y)`.
- Normal form: `R = ⊕_g A u_g` as a left `A`-module. So `g |-> u_g` is an injective homomorphism `Γ -> R^×` when `X ≠ ∅`.
- Rank ultraproduct: for sizes `N_n` and a nonprincipal ultrafilter `ω`, `M_ω = ∏_ω M_(N_n)(k) / J_ω`, where
  `J_ω = {(x_n) : lim_ω rank(x_n)/N_n = 0}`. Since `rank(xy) <= min(rank x, rank y)` and rank is subadditive, `J_ω` is a
  two-sided ideal.

## 1. Følner rank models for minimal actions of amenable groups

**Theorem F.** Let `Γ` be countable amenable, `Γ ↷ X` minimal with `X` infinite, and `k` a field. Then `R = LC(X,k) ⋊ Γ`
has an injective unital ring homomorphism into a rank ultraproduct `M_ω` over `k`. Hence `R` carries a faithful Sylvester
matrix rank function and is stably finite.

*Proof.*
1. **The orbit representation.** Fix `x ∈ X`. On `V = k^(Γ)`, with basis `δ_h`, put
   `ρ(f) δ_h = f(h x) δ_h` and `ρ(u_g) δ_h = δ_(gh)`. Then
   `ρ(u_g) ρ(f) ρ(u_g)^(-1) δ_h = f(g^(-1) h x) δ_h = ρ(g.f) δ_h`, so `ρ` is a unital representation of `R`.
   - For `a = Σ_(g∈K) f_g u_g` we get `ρ(a) δ_h = Σ_(g∈K) f_g(g h x) δ_(gh)`, which lies in the span of the `δ_(gh)`,
     `g ∈ K`.
2. **Truncation and defect.** Let `(F_n)` be a left Følner sequence (`|g F_n Δ F_n|/|F_n| -> 0` for every `g`). Let `P_n`
   be the coordinate projection onto `span{δ_h : h ∈ F_n}`, and `ψ_n(a) = P_n ρ(a) P_n ∈ M_(|F_n|)(k)`.
   - `ψ_n` is `k`-linear and unital.
   - `ψ_n(a) ψ_n(b) - ψ_n(ab) = -P_n ρ(a)(1 - P_n) ρ(b) P_n`.
   - If `b` is supported on `K_b`, the rank of that defect is at most `|{h ∈ F_n : K_b h ⊄ F_n}|`, which is at most
     `Σ_(g∈K_b) |g F_n Δ F_n| = o(|F_n|)`.
   - So `Ψ(a) = [(ψ_n(a))_n]` is a unital ring homomorphism `R -> M_ω`.
3. **Faithfulness.** Let `0 ≠ a = Σ_(g∈K) f_g u_g`, and pick `g_0 ∈ K` with `f_(g_0) ≠ 0`.
   - Choose `c ≠ 0` and a nonempty clopen `W'` on which `f_(g_0) ≡ c`, and put `W = g_0^(-1) W'`.
   - **A private coordinate.** If `h x ∈ W`, the `δ_(g_0 h)` coordinate of `ρ(a) δ_h` is exactly `f_(g_0)(g_0 h x) = c`.
     Any other `g ∈ K` lands on `δ_(gh) ≠ δ_(g_0 h)`.
   - **Syndetic visits.** By minimality every orbit meets the open set `W`. By compactness there is a finite `L ⊆ Γ` such
     that every `y` has some `l ∈ L` with `l y ∈ W`.
     - For `h ∈ F_n` with `L h ⊆ F_n`, choose such `l(h)`. The map `h |-> l(h) h` into
       `E_n = {h' ∈ F_n : h' x ∈ W}` is at most `|L|`-to-one.
     - So `|E_n| >= |{h : Lh ⊆ F_n}| / |L| >= |F_n|/|L| - o(|F_n|)`.
   - **Separation.**
     - Let `E'_n = {h ∈ E_n : K h ⊆ F_n}`. Then `|E'_n| >= |F_n|/|L| - o(|F_n|)`.
     - Choose greedily `H_n ⊆ E'_n` with `K h ∩ K h' = ∅` for `h ≠ h'` in `H_n`. Each choice excludes at most `|K^(-1)K|`
       elements, so `|H_n| >= |E'_n| / |K^(-1) K|`.
     - For `h ∈ H_n`, the vectors `ψ_n(a) δ_h = ρ(a) δ_h` are nonzero and have pairwise disjoint supports inside `K h`, so
       they are linearly independent.
   - Hence `rank ψ_n(a) / |F_n| >= 1/(|L| |K^(-1) K|) - o(1)`, and `Ψ(a) ≠ 0`.
4. **Consequences.** `rk(a) = lim_ω rank ψ_n(a)/|F_n|` is a unital Sylvester matrix rank function, faithful on each
   `M_m(R)`: entries have rank at most that of the matrix. `M_m(M_ω)` is a rank ultraproduct, hence directly finite. ∎

**Remarks.**
- Freeness is not used. Minimality is essential: for the trivial action on a Cantor set the truncations have a kernel.
- This is the standard Følner truncation technique: repo box version `free-minimal-crossed-products-are-simple-with-rank-models`
  for `Z^d`, published `Z` case `cantor-z-crossed-product-embeds-in-continuous-factor` (Ara–Claramunt).
- It gives rank models, not exact ones. Exact models force residually finite behaviour (Section 4).

## 2. The acting group inside the projective elementary group

**Lemma W.** Let `R` be a unital ring, `N >= 2`, and `θ : Γ -> R^×` an injective homomorphism. Then
`ι(g) = diag(θ(g), θ(g)^(-1), 1_(N-2))` defines an injective homomorphism `Γ -> EL_N(R)`. For `N >= 3`, `ι(Γ)` meets the
centre of `EL_N(R)` trivially, so `Γ` embeds in `EL_N(R)/Z(EL_N(R))`.

*Proof.*
- **Whitehead's identity.** For a unit `v`, put `w(v) = x_12(v) x_21(-v^(-1)) x_12(v)`.
  - Row by row, `x_12(v) x_21(-v^(-1)) = [[1 - v v^(-1), v], [-v^(-1), 1]] = [[0, v], [-v^(-1), 1]]`.
  - Then `w(v) = [[0, v], [-v^(-1), 0]]`.
  - So `w(v) w(-1) = [[0, v], [-v^(-1), 0]] · [[0, -1], [1, 0]] = diag(v, v^(-1))`, and `diag(v, v^(-1)) ∈ E_2(R) ⊆ EL_N(R)`.
- **The homomorphism.** `ι` is a homomorphism because `θ` is, and it is injective because `θ` is.
- **Trivial centre intersection.** If `ι(g)` is central in `EL_N(R)` (`N >= 3`), it commutes with `x_13(1)`. But
  `ι(g) x_13(1) ι(g)^(-1) = I + θ(g) E_13 = x_13(θ(g))`, so `θ(g) = 1` and `g = e`. ∎

For a crossed product, `θ(g) = u_g`. Units of topological full-group type embed the same way.

## 3. Finitely presented LEF groups are residually finite

**Lemma P** (standard). A finitely presented LEF group is residually finite.

*Proof.*
- Let `Γ = ⟨S | R_0⟩` with `S = S^(-1)` finite and `R_0` finite, and let `g ≠ e` be given by a word `w`.
- Let `B` be the ball of radius `r` in the word metric, with `r` at least the lengths of `w` and of every relator. LEF gives
  a finite group `Q` and an injective `φ : B -> Q` with `φ(ab) = φ(a)φ(b)` whenever `a, b, ab ∈ B`.
- `φ(e) = φ(e)^2`, so `φ(e) = e`, and `φ(s^(-1)) = φ(s)^(-1)`. Define `θ` on the free group by `θ(s) = φ(s)`.
- By induction on length, `θ(v) = φ(v̄)` for every word `v` whose prefixes all evaluate in `B`. That covers every relator
  and `w`.
- So `θ` kills `R_0` and factors through `Γ`, and `θ(w) = φ(g) ≠ φ(e) = e`. ∎

## 4. The object

**Inputs, all on main.**
- `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`. For each prime `p` there is a finitely presented amenable
  group `Γ_p` with a nonidentity central `c_p` killed by every exact finite-dimensional unitary representation (APQ1).
  - **`Γ_p` is not residually finite.** For a finite quotient `π : Γ_p -> Q`, the regular representation of `Q` is faithful,
    finite-dimensional and unitary, so it kills `π(c_p)`. Hence `π(c_p) = e`.
  - By Lemma P, `Γ_p` is not LEF.
- `gjs-countable-groups-have-free-minimal-subflows` (Gao–Jackson–Seward, Theorem `INTRO PERFDENSE`): `2^Γ` contains a
  minimal hyper aperiodic point `x`, and `X = cl(Γ x)` is a free minimal subflow.
  - `X` is infinite, since orbits are free and `Γ` is infinite.
  - `X` has no isolated point: the isolated points form an open invariant set, so if one existed `X` would be discrete and
    finite. So `X` is a Cantor space.

**Theorem N.** Let `p` be a prime, `Γ = Γ_p`, `X ⊆ 2^Γ` a free minimal subflow, `q` a prime power, and
`R = LC(X, F_q) ⋊ Γ`. For every `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))` is:
1. infinite, finitely generated and simple;
2. Kazhdan;
3. `F_q`-linear sofic;
4. not LEF.

*Proof.*
- **`R` is finitely generated.**
  - Let `χ = 1_([x_e = 1])`. Then `u_g χ u_g^(-1) = g.χ` is the indicator of the translate `g[x_e = 1]`, which is a
    cylinder `[x_h = 1]` (with `h = g` or `g^(-1)`, depending on the shift convention). As `g` ranges over `Γ` every
    coordinate cylinder occurs. So products of translates of `χ` and `1 - χ` give all cylinder indicators, which span
    `LC(X, F_q)`.
  - `F_q = F_p[α]`. So `R` is generated by `χ`, `α`, and the `u_s` for `s` in a finite symmetric generating set of `Γ`.
  - Hence `EL_N(R)` is finitely generated for `N >= 3`: `x_ij(ab) = [x_ik(a), x_kj(b)]`, and root subgroups are additive.
- **(1) Simplicity.**
  - `R ≅ A_(F_q)(X ⋊ Γ)` (`crossed-products-are-transformation-steinberg-algebras`).
  - The transformation groupoid of a free minimal action on a Cantor space is Hausdorff, ample, principal (hence effective)
    and minimal, with compact infinite unit space.
  - `steinberg-elementary-groups-are-simple-mod-centre` gives that `S_N` is infinite and simple, with `Z(EL_N(R)) ⊆ F_q^× 1`.
- **(2) (T).** `elementary-groups-over-fg-rings-have-property-t`, and quotients of Kazhdan groups are Kazhdan.
- **(3) Linear soficity.**
  - Theorem F gives a unital homomorphism into a rank ultraproduct over `F_q`.
  - `R` is simple with centre `F_q` (`minimal-effective-steinberg-algebras-have-scalar-centre`).
  - `rank-modelled-simple-rings-give-linear-sofic-projective-el` makes `EL_N(R)/(EL_N(R) ∩ F_q^× 1)` `F_q`-linear sofic.
  - That quotient is `S_N`: scalars in `EL_N(R)` are central, and the centre is scalar by (1).
- **(4) Not LEF.** Lemma W embeds `Γ_p` in `S_N`, LEF passes to subgroups, and `Γ_p` is not LEF. ∎

**Corollary M** (the UN middle rung). `R` is a finitely generated, infinite, simple unital `F_q`-algebra with a unital rank
model over `F_q` (Theorem F), and `EL_N(R)` is Kazhdan and not LEF for every `N >= 3` (Lemma W, since `Γ_p ≤ EL_N(R)`).
This establishes `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` without finite presentation of the ring and
without quantum tilings.
- By the established direction `exactly-matricial-rings-have-lef-general-linear-groups`, `R` is not exactly matricial.
- So `R` is a concrete simple ring on the measure side with rank models but no exact matricial models.

## 5. Where the rank route stops (firewalls)
- **Soficity.** Rank models give only rank defects. Upgrading `S_N` to sofic is Arzhantseva–Păunescu Question 8.5 at `S_N`
  (`free-minimal-subshift-elementary-groups-are-sofic` records the same block over `Z^2`-SFTs). The known sofic subgroups of
  `S_N` (`Γ_p`, and full-group units via Lemma W) give no obstruction.
- **Hyperlinearity.** Characteristic-`p` rank models carry no Hilbert–Schmidt information, so nothing is claimed.
- **MF.** Operator-norm MF of `S_N` is open (rung M⇐ of the UN root).
- **Non-amenable acting groups.** Theorem F needs Følner sets. For non-amenable `Γ` with an invariant measure, rank models
  in characteristic `p` are open, and `un-tarski` records this as Kaplansky-hard. There Lemma W still transfers non-LEF (and
  non-soficity) from `Γ` to `S_N`, but gives no positive model.
- **Exact models force residual finiteness.** If `R` had exact matricial models over finite fields, every finitely generated
  subgroup of `GL_N(R)` would be LEF (`exactly-matricial-rings-have-lef-general-linear-groups`), including `Γ_p`. So for
  non-LEF `Γ` towers are impossible, whatever the dynamics.

## 6. Calibration
- **`Γ = Z`, the Pestov case.** `Z` is residually finite, and exact towers exist, so `S_N` is LEF. Theorem F reproduces an
  Ara–Claramunt-type rank model, and Lemma P gives no obstruction.
- **Cuntz groupoid, the paradox side.** It is not the transformation groupoid of an amenable group with an invariant
  measure. No rank model exists (`leavitt-algebra-has-no-unital-rank-model`), consistent with Theorem F not applying.
- **Calibration F3** (`group-ring-lef-iff-group-lef-iff-elementary-group-lef`). `EL_N(F_q[Γ])` for amenable non-LEF `Γ` is
  linear sofic and not LEF, but the ring is not simple. Theorem N is the simple-ring, simple-group version of the same
  separation, and its mechanism is the same: a non-LEF group of units.

## 7. Credit and bounds
- **Imports.** Gao–Jackson–Seward (free minimal subflows, verbatim from arXiv:1201.0513 source on MSI); Abels'
  finite-presentation theorem, entering only through the established Abels–Prüfer node; Ershov–Jaikin-Zapirain.
- **Graph dependencies.**
  - The adjoint linear-sofic theorem (established, unreviewed).
  - Uniform simplicity (reviewed PASS).
  - The Steinberg dictionary and scalar centre (unreviewed / PASS).
- **Standard material.** Følner truncation (Elek for amenable group algebras; Ara–Claramunt for `Z`) and Lemma P, written
  out here in full.
- **Novelty.** Bounded to this graph: `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` was OPEN, and no simple
  Kazhdan non-LEF linear sofic group is recorded. No literature search beyond the imports.
