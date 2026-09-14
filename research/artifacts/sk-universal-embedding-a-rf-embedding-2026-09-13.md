# Every finitely generated residually finite group embeds in an infinite simple Kazhdan LEF group

Lane `sk-universal-embedding-a` (SK swarm), 2026-09-13. Written proofs, UNREVIEWED (queued with sk-verify-3).

## 0. Result

**Theorem E.** Every finitely generated residually finite group `Γ` is a subgroup of an infinite, finitely
generated, simple group with property (T) that is LEF, hence sofic and hyperlinear. One can take
`G = EL_3(LC(X,F_2) ⋊ Δ)`, where:
- `Δ ⊇ Γ` is a finitely generated residually finite group with `Γ ≤ [Δ,Δ]` (§2);
- `X ⊆ {0,1}^Δ` is a free minimal Toeplitz subshift with periodic window models (§3).

**Examples.** Every finitely generated linear group (Malcev), `SL_n(Z)`, surface groups, free groups, finitely
generated nilpotent groups and the Grigorchuk group embed in infinite simple Kazhdan LEF groups.

**Prior art.** Without (T), Kionke–Schesler, arXiv:2304.09307, Theorem 1.2 (= Theorem 9.14), quoted verbatim by
sk-questions-ggt (`research/artifacts/sk-questions-ggt-literature-2026-09-13-part1.md` §1 B1): "Let H be a finitely
generated, residually finite (amenable) group. There is a finitely generated, residually finite (amenable) group G
and an infinite, simple, (amenable) LEF group Q such that (1) there is an embedding ι : H → G, (2) there is a
projection π : G → Q, (3) the composition π ◦ ι is injective." Their Q is the head of a telescope of alternating
groups. The new part here is property (T). So every f.g. residually finite group lies both in an amenable simple
LEF group (Kionke–Schesler) and in a Kazhdan simple LEF group (Theorem E).

## 1. Firewall: the obvious embedding misses the elementary group

**Proposition 1.** Let `X ⊆ A^Z` be an infinite minimal subshift, `k` a field, `R = LC(X,k) ⋊ Z`, `n ≥ 1`.
Then `diag(u, 1, …, 1) ∉ E_n(R)`.

*Proof.* Fix `x ∈ X` and let `R` act on `V = ⊕_(t∈Z) k δ_t` by `uδ_t = δ_(t+1)` and `fδ_t = f(T^t x)δ_t`. This
respects `ufu^(-1) = f∘T^(-1)`. `M_n(R)` acts on `V^n`, and every matrix has bounded propagation. Let `P` be the
projection onto the span of `δ_t`, `t ≥ 0`, in each coordinate. For `a ∈ M_n(R)`, `Pa(1−P)` and `(1−P)aP` have
finite rank.
- For `a ∈ GL_n(R)`, `PaP` and `Pa^(-1)P` are inverse modulo finite rank on `PV^n`. So `PaP` has finite-dimensional
  kernel and cokernel, and `ind(a) = dim ker PaP − dim coker PaP` is defined.
- `PabP = PaP·PbP + Pa(1−P)bP`. The index over a field is multiplicative for Fredholm maps and invariant under
  finite-rank perturbation, so `ind` is a homomorphism `GL_n(R) -> Z`.
- For `i ≠ j`, `P e_ij(r) P = P + P rE_ij P`, and `(P rE_ij P)^2 = P rE_ij P rE_ij P = 0`. So `P e_ij(r) P` is
  invertible on `PV^n` and `ind(e_ij(r)) = 0`. Hence `ind` vanishes on `E_n(R)`.
- `P diag(u,1,…,1) P` is the unilateral shift in the first coordinate: injective with one-dimensional cokernel `kδ_0`.
  So its index is `−1`. ∎

For `Γ = Z` a copy inside `EL_3` is `t ↦ diag(u^t, u^(-t), 1)`, by Whitehead's lemma. For nonabelian `Γ` the map
`γ ↦ diag(u_γ, u_γ^(-1), 1)` is not a homomorphism: the product is `diag(u_(γδ), u_(δγ)^(-1), 1)`. So the embedding
needs an overgroup in which `Γ` consists of commutators.

## 2. An overgroup of commutators

**Ore 1951, Theorem 1** (Proc. AMS 2 (1951), 307–314, p. 308, read from the scan): "Every element in the alternating
group A_n is a commutator of Σ_n."

**Lemma 2.** Every finitely generated residually finite group `Γ` embeds in a finitely generated residually finite
group `Δ` with `Γ ≤ [Δ,Δ]`. If `Γ` is infinite, so is `Δ`.

*Proof.* Let `S` be a finite generating set and `Γ_n` normal subgroups of finite index with `∩ Γ_n = {e}`.
- Let `Ω_n = Γ/Γ_n × {1,2}`. Left multiplication `λ_n(γ)(gΓ_n, i) = (γgΓ_n, i)` is a permutation whose cycles occur
  in pairs of equal length, so it is even.
- `ρ = (λ_n)_n : Γ -> P = ∏_n Sym(Ω_n)` is an injective homomorphism.
- By Ore's Theorem 1 applied in each coordinate, every `s ∈ S` has `ρ(s) = [a_s, b_s]` with `a_s, b_s ∈ P`.
- Let `Δ = ⟨ρ(S), a_s, b_s : s ∈ S⟩ ≤ P`. It is finitely generated. It is residually finite, because the
  projections `P -> Sym(Ω_n)` are homomorphisms to finite groups that separate the points of `P`.
- Then `ρ(s) ∈ [Δ,Δ]` for all `s ∈ S`, so `ρ(Γ) ≤ [Δ,Δ]`. ∎

The same proof gives: every f.g. LEF group `Γ` embeds in a f.g. LEF group `Δ` with `Γ ≤ [Δ,Δ]`. Embed `Γ` in an
algebraic ultraproduct of finite symmetric groups, double the sets, and take `Δ` inside that ultraproduct. A f.g.
subgroup of an algebraic ultraproduct of finite groups is LEF.

## 3. Toeplitz subshift: free, minimal, with periodic window models

Let `Δ` be finitely generated, infinite and residually finite.
- Fix a chain `Δ = Δ_0 ≥ Δ_1 ≥ …` of finite-index normal subgroups with trivial intersection.
- Fix word-metric balls `B_m` and an enumeration `g_1, g_2, …` of `Δ`.
- Pass to a subsequence so that `d_m = [Δ_(m−1):Δ_m] ≥ 2|B_(m−1)| + m + 2`.
- Put `C_0 = Δ`. At level `m`, choose among the `d_m` cosets of `Δ_m` in the hole `C_(m−1)` a new hole `C_m`
  avoiding `g_1, …, g_m`. Set `x = 1` on one other coset and `x = 0` on the remaining ones.
- Let `X` be the orbit closure of `x` under `(g·y)(h) = y(g^(-1)h)`.

This is the construction of Theorem T (`rf-toeplitz-subshifts-over-residually-finite-groups`, reviewed PASS). It
already gives:
- `x` is defined everywhere;
- `X` is minimal;
- periodic window models (below);
- the orbit of `x` is free.

The lemma below upgrades the last point to freeness at EVERY point, which the note's self-contained tower argument
uses. Corollary T itself used Steinberg simplicity, which needs only topological freeness.

**Lemma 3 (free at every point).** Every `y ∈ X` has, for each `m`, exactly one coset `D_m(y)` of `Δ_m` on which
`y` is not constant. Moreover `D_(m+1)(y) ⊆ D_m(y)` and `D_m(g·y) = g D_m(y)`. So the action of `Δ` on `X` is free.

*Proof.*
- (F1) `x` is constant on every coset of `Δ_m` except `C_m`. (F2) `x` equals `1` on a whole coset of `Δ_(m+1)` inside
  `C_m`, and `0` on another.
- So `g·x` is constant off `gC_m` and not constant on `gC_m`.
- Let `y = lim g_k·x`. Since `Δ/Δ_(m+1)` is finite, some residue `g_kΔ_(m+1)` repeats along a subsequence. There
  `gC_m = D` is fixed, and so are the two cosets `E_1, E_0 ⊆ D` of `Δ_(m+1)` where `g_k·x` is `1`, resp. `0`.
- Pointwise limits keep equalities, so `y` is constant on every coset of `Δ_m` other than `D`, while `y|_(E_1) = 1`
  and `y|_(E_0) = 0`. Hence `D_m(y) := D` is the unique non-constant coset.
- Nesting: a coset of `Δ_(m+1)` inside a constant coset of `Δ_m` is constant. Equivariance is clear.
- If `g·y = y`, then `gD_m(y) = D_m(y)`. With `D_m(y) = cΔ_m` this means `c^(-1)gc ∈ Δ_m`, i.e. `g ∈ Δ_m` by
  normality, for every `m`. So `g = e`. ∎

`y ↦ (D_m(y))_m` is the equivariant factor map onto the odometer `lim Δ/Δ_m`. Lemma 3 says `X` is an extension of a
free action.

**Lemma 4 (periodic window models).** For finite `W, F ⊆ Δ` there are `M` and a `Δ_M`-invariant `p ∈ {0,1}^Δ` with
`Δ_M ∩ F^(-1)F = {e}` and `{(g^(-1)·p)|_W : g ∈ Δ} = L_W(X)`.

*Proof.* Theorem T, part 2, where `M` may be enlarged at will.
- Choose `M` with `W ⊆ B_M`, `Δ_M ∩ F^(-1)F = {e}`, and every `W`-pattern of `X` occurring in `x` at some `g` with
  `gW ∩ C_M = ∅`.
- Put `p = x` off `C_M` and `p = 0` on `C_M`. It is `Δ_M`-invariant by (F1).
- Fix `g`. For `γ ∈ Δ_M` and `w ∈ W`: if `gw ∉ C_M` then `x(γgw) = x(gw) = p(gw)`, since `γgw ∈ Δ_M gw`. If
  `gw ∈ C_M`, then `γ̄ ↦ γgwΔ_(M+1)` is a bijection from `Δ_M/Δ_(M+1)` onto the cosets of `Δ_(M+1)` in `C_M`. Only two
  of them are bad: the `1`-coset and `C_(M+1)`.
- At most `2|W| ≤ 2|B_M| < d_(M+1)` classes are bad in total. A good `γ` gives `x(γgw) = p(gw)` for all `w ∈ W`, so
  every `W`-pattern of `p` is a pattern of `x`.
- Coverage holds by the choice of `M`. ∎

## 4. The simple Kazhdan LEF group over Δ

**Proposition 5.** Let `Δ` be finitely generated and infinite, and `X ⊆ A^Δ` a free minimal subshift with the
property of Lemma 4. Then `G = EL_3(LC(X,F_2) ⋊ Δ)` is an infinite, finitely generated, simple group with property
(T) that is LEF.

*Proof.* The proof of the note's Theorem 1 (`$SK/manuscript-disk-1646.tex` l.67–227), with these replacements.
- **Ring.** `R = {Σ f_g u_g}`, with `u_g f u_g^(-1) = f∘g^(-1)`, so `u_g e_V u_g^(-1) = e_(gV)`. `R` is generated by
  `u_s^(±1)` (`s ∈ S`) and the letter indicators. (T) comes from EJZ Theorem 1.1. `G` is infinite because
  `e_12(LC(X,F_2))` is.
- **Simplicity of R, `Z(R) = F_2`, `Z(G) = 1`.** Verbatim, with `T^j` replaced by `g`: freeness gives clopen `U` with
  `U ∩ gU = ∅` for the finitely many `g ≠ e` occurring.
- **LEF.** The model is `F_2^(Δ/Δ_M)`, with `u_g δ_(hΔ_M) = δ_(ghΔ_M)` and `D(f)δ_(hΔ_M) = f(h·p)δ_(hΔ_M)` (well
  defined because `p` is `Δ_M`-invariant). Then `P_g D(f) P_g^(-1) = D(f∘g^(-1))`. Every window of every `h·p` lies
  in `L(X)`, so listed products are preserved. Every pattern of `X` occurs, so nonzero coefficients stay nonzero. And
  `Δ_M ∩ F^(-1)F = {e}` separates the supports of distinct `P_g`.
- **Towers.** For finite `B ∋ e` and clopen `U` with `U ∩ β^(-1)β'U = ∅` for `β ≠ β' ∈ B`, put
  `E_(β,β')(W) = e_(βW) u_(ββ'^(-1))`, `W ⊆ U`. Then
  `E_(β,β')(W) E_(δ,δ')(W') = e_(βW) e_(ββ'^(-1)δW') u_(ββ'^(-1)δδ'^(-1))`, which is `E_(β,δ')(W∩W')` if `β' = δ`
  and `0` otherwise. So the span is `M_B(LC(U,F_2))`.
- **Absorption.** `fu_γ · E_(β,β')(W) = E_(γβ,β')(W_1)` and `E_(β,β')(W) · f'u_γ = E_(β,γ^(-1)β')(W_2)`. So entries
  supported in `B_w` send the `B_1`-tower into the `B_(w+1)`-tower.
- **Choices.** Take a clopen partition with `C ∩ gC = ∅` for `e ≠ g ∈ B_(2w+2)`. Then `e_C = E_(e,e)(C)` and
  `e_Cu_s = E_(e,s^(-1))(C)` lie in the `B_1`-tower over `U = C`, and `d = 3|B_(w+1)| ≥ 3`. The copy `H_W` of
  `GL_d(F_2)` is generated by `e_pq(E_(β,β')(W))` and the commutators
  `[e_pq(E_(β,β')(W)), e_qp(E_(β',β')(W))] = I + E_(β,β')(W)E_pp`. The rest is verbatim. ∎

This is `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (reviewed PASS; its simplicity step goes
through `steinberg-elementary-groups-are-simple-mod-centre`) with a self-contained simplicity proof. Lane
sk-general-actions-a is landing the general form of the note's proof over f.g. groups.

## 5. Proof of Theorem E

- **Finite `Γ`.** `Γ ≤ Sym(d) ≤ GL_d(F_2) ≅ H_W ≤ G_X` for any infinite minimal `Z`-subshift `X` and a tower of height
  `d/3` (note l.205–215).
- **Infinite `Γ`.** Take `Δ` from Lemma 2, `X` from §3, and `G = EL_3(R)`, `R = LC(X,F_2) ⋊ Δ`, from Proposition 5.
- **Whitehead.** For a unit `c` of any ring, `w(c) = e_12(c) e_21(−c^(-1)) e_12(c) = [[0,c],[−c^(-1),0]]`, so
  `w(c)w(−1) = diag(c, c^(-1)) ∈ E_2`. For units `a, b`: `diag(a,a^(-1)) diag(b,b^(-1)) diag((ba)^(-1), ba) =
  diag(aba^(-1)b^(-1), 1)`. So `diag([a,b], 1, 1) ∈ E_3(R)` (`perfect-unit-subgroups-elementary-proof`, steps 1–2).
- **Embedding.** `δ ↦ u_δ` is an injective homomorphism `Δ -> R^×`. For `γ ∈ Γ`, `ρ(γ)` is a product of commutators in
  `Δ`, so `ψ(γ) = diag(u_(ρ(γ)), 1, 1)` lies in `E_3(R) = G`. So `ψ : Γ -> G` is an injective homomorphism. ∎

## 6. Credit and bounds

- **Kionke–Schesler Theorem 1.2:** the f.g. simple LEF envelope without (T); cite it as the amenable/no-(T) counterpart.
- **Toeplitz subshifts over residually finite groups:** Krieger (2010), Cortez–Petite (2008), and Cecchi-Bernales–Cortez–Gómez for
  unique ergodicity. The sparse filling and the RF design are `un-rf-beyond-free` §6 (Theorem T).
- **Other imports:** Ore 1951 Theorem 1 (verified from the scan); Whitehead's lemma (standard, e.g. Milnor,
  *Introduction to algebraic K-theory*, Lemma 3.1); EJZ Theorem 1.1; Ma arXiv:2209.00580 Theorem C
  (topological full groups of RF actions are LEF; not used, but the natural group-level neighbor).
- **Search bound:** two web searches ("every finitely generated residually finite group embeds in a finitely generated
  simple group property (T)"; a Kazhdan/LEF/sofic embedding search) plus sk-questions-ggt's literature part 1. No
  simple Kazhdan LEF envelope for residually finite groups was found, and none could predate infinite simple Kazhdan
  LEF groups. Embeddings into simple Kazhdan groups without approximation properties were not searched in depth
  (e.g. via Gromov/Ol'shanskii quotients of hyperbolic Kazhdan groups).

## 7. The LEF case is open

**Question.** Does every finitely generated LEF group embed in an infinite finitely generated simple Kazhdan LEF
group? Equivalently, as the converse is automatic: is LEF exactly the class of f.g. subgroups of such groups?

**Where the approaches stop.**
- **Overgroup.** Solved for LEF input (§2): `Γ ≤ [Δ,Δ]` with `Δ` f.g. LEF.
- **Toeplitz levels.** Levels are finite-index subgroups of the acting group. The freeness argument (Lemma 3) needs
  trivial intersection, which forces the acting group to be residually finite.
- **Genuine finite models.** Kerr–Nowak RF models of a free action separate the elements of each finite set, which
  forces a residually finite acting group (also found by sk-general-actions-a).
- **Ultralimit subshifts along partial LEF models `(Q_n, φ_n)`.** Color each `Q_n` by `c_n`, and let `L_W` consist of
  the patterns occurring for `ω`-most `n`.
  - Exact window models are automatic: a window has finitely many patterns, so `L_W(Q_n,c_n) = L_W` for `ω`-most `n`,
    and the crossed product embeds in `∏_ω M_(|Q_n|)(F_2)`.
  - What is missing is minimality and freeness with bounds uniform in `n`.
  - Internal "levels" of bounded index give genuine finite quotients of the acting group, which forces RF again.
  - Internal levels of unbounded index destroy uniform syndeticity.
  - Random colorings give the full shift.
- **Possible ways around.**
  - Use topological freeness with Steinberg simplicity, which only needs a dense set of free points.
  - Leave crossed products and find simple LEF rings with local matrix units that contain `F_2[Δ]`.
