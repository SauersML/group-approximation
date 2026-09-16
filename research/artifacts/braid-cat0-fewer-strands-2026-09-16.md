# CAT(0) braid groups pass to fewer strands (2026-09-16)

Agent `hi-spec-zaremsky-3-06-braid-groups-cat`, angle "special case /
strengthening" on `zaremsky-3-06-braid-groups-cat0`. This is the full proof for
route `braid-cat0-passes-to-fewer-strands-proof`, which establishes claim
`braid-cat0-passes-to-fewer-strands`. It also supports the reduction route
`every-braid-group-cat0-from-infinitely-many-strands`.

## 0. Statement, conventions, inputs

A group `G` **acts geometrically** on a metric space `X` if it acts by
isometries, **properly** (every `x ∈ X` has `r_x > 0` such that
`F(x, r_x) = {g : g B(x, r_x) ∩ B(x, r_x) ≠ ∅}` is finite; Bridson–Haefliger
I.8.2) and **cocompactly** (`X = G·K` for some compact `K`). `G` is **CAT(0)**
if it acts geometrically on a complete CAT(0) space. This is the meaning in
`every-braid-group-is-cat0` and in Zaremsky Problem 3.6.

**Theorem M.** Let `n ≥ 1`. If `B_{n+1}` is CAT(0), then `B_n` is CAT(0).

**Proposition G (general form).** Let `G` act geometrically on a complete CAT(0)
space `X`. Let `γ ∈ G` and suppose the centralizer `C_G(γ)` is an internal direct
product `H × ⟨z⟩` with `z` of infinite order. Then `H` acts geometrically on a
complete CAT(0) space.

**Proposition B (braid centralizer).** Let `n ≥ 2`, let `ι : B_n → B_{n+1}` add a
straight last strand, and let `Δ²_m` denote the full twist in `B_m`. Then
`C_{B_{n+1}}(ι(Δ²_n)) = ι(B_n) × ⟨Δ²_{n+1}⟩`, an internal direct product, with
`ι` injective and `Δ²_{n+1}` of infinite order.

Theorem M is Proposition G applied to Proposition B (§5).

**Standard inputs used without re-proof.**
- (BH1) *Convexity of the metric* (Bridson–Haefliger II.2.2): in a CAT(0) space,
  for geodesics `c, c'` parametrized proportionally to arc length on `[0,1]`,
  `t ↦ d(c(t), c'(t))` is convex.
- (BH2) *Hyperbolic isometries* (Bridson–Haefliger II.6.8; the same statement is
  used in the COMPLETE route `kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers-proof`).
  Let `z` be a hyperbolic isometry of a complete CAT(0) space `M`, with
  `|z| = inf_x d(x, zx) > 0` attained. Then `Min(z) = {x : d(x, zx) = |z|}` is
  isometric to a product `Y × R`, and `z` acts on it as `(y, t) ↦ (y, t + |z|)`.
  Every isometry `α` of `M` commuting with `z` preserves `Min(z)`, and its
  restriction has the form `(α', α'')` with `α' ∈ Isom(Y)` and `α''` a
  translation of `R`.
- (HR) *Hopf–Rinow–Cohn-Vossen* (Bridson–Haefliger I.3.7): a complete, locally
  compact length space is proper.
- (FN) *Fadell–Neuwirth fibration* (E. Fadell, L. Neuwirth, Math. Scand. 10
  (1962); classical, see also J. Birman, *Braids, links, and mapping class
  groups*, 1974, Chapter 1; neither re-read in this pass). Forgetting the last
  point, `Conf_{n+1}(C) → Conf_n(C)`, is a locally trivial fibration with fibre
  `C ∖ {n points}`. By induction on `n` every `Conf_n(C)` is aspherical, so the
  long exact sequence gives a short exact sequence
  `1 → π_1(C ∖ {n points}) → P_{n+1} → P_n → 1`. In particular the kernel of
  forgetting the last strand of a pure braid is a free group.
- (NS) *Nielsen–Schreier*: subgroups of free groups are free. So two commuting
  elements of a free group generate a free abelian, hence cyclic, subgroup.

Everything else is proved below.

## 1. Three facts about geometric actions

Throughout this section `G` acts geometrically on a complete CAT(0) space `X`,
with compact `K`, `GK = X`, and `K ⊆ B̄(x_0, R)`. For `S ⊆ X` write
`F_S = {g ∈ G : gS ∩ S ≠ ∅}`.

**Lemma 1.1 (finite return sets).** For every compact `S ⊆ X`, `F_S` is finite.
(Only properness is used, not completeness.)

*Proof.* Suppose infinitely many distinct `g_j` satisfy `g_j c_j = c'_j` with
`c_j, c'_j ∈ S`. Pass to a subsequence with `c_j → c` and `c'_j → c'`. Then
`d(g_j c, c') ≤ d(g_j c, g_j c_j) + d(c'_j, c') → 0`. Let `r = r_c` be the
properness radius at `c`. For `j, l ≥ j_0` we get `d(g_j c, c') < r/2`, so
`d(g_l⁻¹ g_j c, c) = d(g_j c, g_l c) < r`. Hence `g_l⁻¹ g_j c` lies in
`g_l⁻¹ g_j B(c, r) ∩ B(c, r)`, so `g_l⁻¹ g_j ∈ F(c, r)`. Fix `l = j_0`. Then
infinitely many distinct `g_j` lie in the finite set `g_l F(c, r)`, a
contradiction. ∎

**Lemma 1.2 (properness of `X`).** `X` is a proper metric space.

*Proof.* This is the lemma of the COMPLETE route
`braid-proper-cat0-action-from-geometric-action`, repeated for completeness.
1. *Uniform radius.* Cover `K` by finitely many balls `B(k_i, r_i/2)` with
   `r_i = r_{k_i}`, and put `r = min_i r_i/2`. If `k ∈ B(k_i, r_i/2)` then
   `B(k, r) ⊆ B(k_i, r_i)`, so `F(k, r) ⊆ F(k_i, r_i)` is finite.
2. *Small balls meet finitely many translates of `K`.* Let `ε = r/4` and
   `x ∈ X`. Since `gK ∩ B(g_0 k_0, ε) ≠ ∅` iff `g_0⁻¹g K ∩ B(k_0, ε) ≠ ∅`, we
   may assume `x ∈ K`. Suppose infinitely many distinct `g_j` have
   `g_j k_j ∈ B(x, ε)` with `k_j ∈ K`. Pass to a subsequence with `k_j → k ∈ K`
   and `d(k_j, k) < ε` for all `j`. Then `d(g_j k, x) < 2ε`, so
   `d(g_j k, g_l k) < 4ε = r` and `g_l⁻¹ g_j ∈ F(k, r)`. Fixing `l` gives a
   contradiction as in Lemma 1.1.
3. So `B(x, ε)` lies in a finite union of translates of `K`. That union is
   compact, so `B̄(x, ε/2)` is compact. `X` is complete, geodesic and locally
   compact, hence proper by (HR). ∎

**Lemma 1.3 (semisimplicity).** Let `γ ∈ G`, `|γ| = inf_x d(x, γx)` and
`Min(γ) = {x : d(x, γx) = |γ|}`.
- (a) `Min(γ)` is nonempty, closed and convex.
- (b) `Min(γ)` is invariant under `C_G(γ)`.
- (c) If `γ` has infinite order, then `|γ| > 0`.

*Proof.* (a) *Nonempty.* Choose `x_j` with `d(x_j, γx_j) → |γ|` and
`d(x_j, γx_j) ≤ |γ| + 1`. Choose `g_j` with `k_j = g_j⁻¹ x_j ∈ K`, and put
`h_j = g_j⁻¹ γ g_j`. Then `d(h_j k_j, k_j) = d(γx_j, x_j) ≤ |γ| + 1`, so `k_j`
and `h_j k_j` both lie in `S = B̄(x_0, R + |γ| + 1)`, which is compact by
Lemma 1.2. So `h_j ∈ F_S`, a finite set by Lemma 1.1. Pass to a subsequence with
`h_j = h` constant and `k_j → k ∈ K`. Then
`d(hk, k) ≤ 2 d(k_j, k) + d(h k_j, k_j) → |γ|`, so `d(hk, k) ≤ |γ|`. Fix one
index `j` of the subsequence and put `g = g_j`. Then `γ g = g h`, so
`d(γ gk, gk) = d(hk, k) ≤ |γ|`, and `gk ∈ Min(γ)`.

*Closed.* The displacement `x ↦ d(x, γx)` is continuous.

*Convex.* Let `x, y ∈ Min(γ)` and let `c` be the geodesic from `x` to `y`. Then
`γ∘c` is the geodesic from `γx` to `γy`. By (BH1), `t ↦ d(c(t), γc(t))` is
convex. It is `≤ |γ|` at the endpoints, hence `≤ |γ|` throughout, and `≥ |γ|` by
definition. So `c` lies in `Min(γ)`.

(b) If `cγ = γc`, then `d(cx, γcx) = d(cx, cγx) = d(x, γx)`.

(c) If `|γ| = 0`, then by (a) some `x` has `γx = x`. So every power `γ^k` lies
in `F_{{x}}`, which is finite by Lemma 1.1, and `γ` has finite order. ∎

## 2. Centralizers act geometrically on Min-sets

**Proposition 2.1.** Let `G` act geometrically on a complete CAT(0) space `X`
and let `γ ∈ G`. Then `C_G(γ)` acts geometrically on `Min(γ)`, and `Min(γ)`
with the restricted metric is a complete CAT(0) space.

*Proof.*
- *The space.* By Lemma 1.3(a), `Min(γ)` is nonempty, closed and convex. A
  closed convex subset of a complete CAT(0) space contains the geodesics between
  its points, so it is geodesic with the restricted metric. Its geodesic
  triangles are geodesic triangles of `X`, so they satisfy the CAT(0) inequality.
  It is complete because it is closed.
- *Isometric action.* By Lemma 1.3(b), `C = C_G(γ)` preserves `Min(γ)`.
- *Proper.* For `x ∈ Min(γ)`, the set of `c ∈ C` with
  `c(B(x, r_x) ∩ Min(γ)) ∩ (B(x, r_x) ∩ Min(γ)) ≠ ∅` is contained in `F(x, r_x)`,
  which is finite.
- *Cocompact.* Let `S = B̄(x_0, R + |γ|)`, compact by Lemma 1.2. Then
  `F_S` is finite (Lemma 1.1). Let `h_1, …, h_m` be the elements of `F_S` that
  are conjugate to `γ`, and choose `g_i` with `g_i⁻¹ γ g_i = h_i`. Let
  `x ∈ Min(γ)`, choose `g` with `k = g⁻¹x ∈ K`, and put `h = g⁻¹ γ g`. Then
  `d(hk, k) = d(γx, x) = |γ|`, so `k` and `hk` lie in `S` and `h ∈ F_S`. So
  `h = h_i` for some `i`. Then `g g_i⁻¹` commutes with `γ`, because
  `(g g_i⁻¹)⁻¹ γ (g g_i⁻¹) = g_i h g_i⁻¹ = γ`. Hence `g = c g_i` with `c ∈ C`, and
  `x = c g_i k ∈ C·K''`, where `K'' = g_1 K ∪ … ∪ g_m K` is compact. Put
  `L = Min(γ) ∩ K''`, compact because `Min(γ)` is closed. If `x = c k''` with
  `c ∈ C` and `k'' ∈ K''`, then `k'' = c⁻¹x ∈ Min(γ)` by Lemma 1.3(b), so
  `k'' ∈ L`. Therefore `C·L = Min(γ)`. ∎

*Remark.* This is the familiar statement that in a CAT(0) group, the centralizer
of an element acts cocompactly on its Min-set (compare Bridson–Haefliger II.6.10,
not re-read). The proof above is self-contained given (BH1) and (HR).

## 3. Splitting off a central infinite cyclic factor

**Proposition 3.1.** Let `G` act geometrically on a complete CAT(0) space `M`,
and let `z ∈ G` be central of infinite order. Then `G/⟨z⟩` acts geometrically
on a complete CAT(0) space `Y`. In particular, if `G = H × ⟨z⟩` is an internal
direct product, then `H ≅ G/⟨z⟩` is CAT(0).

*Proof.*
1. *Reduce to `Min(z)`.* `z` is central, so `C_G(z) = G`. By Proposition 2.1,
   `G` acts geometrically on the complete CAT(0) space `M_z = Min(z)`. By
   Lemma 1.2, applied to this action, `M_z` is proper. By Lemma 1.3(a),(c),
   `|z| > 0` and it is attained, so `z` is a hyperbolic isometry of `M`.
2. *Split.* By (BH2) there is an isometry `M_z ≅ Y × R` with
   `z|_{M_z} = (id_Y, t ↦ t + |z|)`. Every `g ∈ G` commutes with `z`, so
   `g|_{M_z} = (g', τ_{s(g)})`, where `g' ∈ Isom(Y)` and `τ_s` is translation by
   `s`. A product map determines its factors (`g'(y)` is the `Y`-coordinate of
   `g(y, 0)`), so `g ↦ g'` is a homomorphism `G → Isom(Y)` with `z' = id_Y`.
   It factors through an action of `Ḡ = G/⟨z⟩` on `Y`.
3. *`Y` is complete CAT(0).* `Y × {0}` is closed and convex in `Y × R`: a
   geodesic between points with second coordinate `0` has second coordinate `0`
   throughout. So `Y` is isometric to a closed convex subset of `M_z`, hence
   complete and CAT(0) (as in Proposition 2.1).
4. *Cocompact.* Let `L ⊆ M_z` be compact with `G·L = M_z`, and let
   `p : M_z → Y` be the projection. It is continuous and satisfies
   `p(gx) = g'p(x)`. So `p(L)` is compact and `Y = p(G·L) = Ḡ·p(L)`.
5. *Proper.* Fix `y ∈ Y` and let `S = B̄((y, 0), 1 + |z|) ⊆ M_z`. `S` is compact
   because `M_z` is proper, so `F_S` is finite by Lemma 1.1, applied to the
   action of `G` on `M_z`. Let `g ∈ G` with `g'B(y, 1) ∩ B(y, 1) ≠ ∅`: pick
   `y_1` with `d(y_1, y) < 1` and `d(g'y_1, y) < 1`. Choose `m ∈ Z` with
   `|s(g) + m|z|| ≤ |z|/2`. Then `g z^m` has `(g z^m)' = g'` and
   `(g z^m)(y_1, 0) = (g'y_1, s(g) + m|z|)`, so
   `d((g z^m)(y_1, 0), (y, 0))² < 1 + |z|²/4 ≤ (1 + |z|)²`. Also
   `d((y_1, 0), (y, 0)) < 1`. So `g z^m ∈ F_S`. Hence every coset `g⟨z⟩` with
   `g'B(y, 1) ∩ B(y, 1) ≠ ∅` meets the finite set `F_S`, and there are only
   finitely many such cosets.
6. *Direct products.* If `G = H × ⟨z⟩`, the quotient map restricts to an
   isomorphism `H → G/⟨z⟩`. ∎

**Proof of Proposition G.** By Proposition 2.1, `C_G(γ) = H × ⟨z⟩` acts
geometrically on the complete CAT(0) space `Min(γ)`. Proposition 3.1 applies. ∎

*Remarks.*
- A geometric action may have a finite kernel. In step 5 the kernel of `Ḡ` on
  `Y` is finite, as properness requires.
- With `G = ⟨z⟩` the proposition recovers the trivial group acting on a point.
  It says nothing new about `Z`.

## 4. The centralizer of `Δ²_n` in `B_{n+1}`

### 4.1 Conventions

- `Conf_m(C)` is the space of ordered `m`-tuples of distinct points, and
  `UConf_m(C) = Conf_m(C)/S_m`. Basepoints are `x_m = (1, 2, …, m)` and its
  image `{1, …, m}`.
- `B_m = π_1(UConf_m(C), {1, …, m})` and `P_m = π_1(Conf_m(C), x_m)`. Paths are
  composed left to right.
- A braid `β` lifts to a path `β̃` in `Conf_m(C)` from `x_m` to
  `(σ_β(1), …, σ_β(m))` for a permutation `σ_β`. `β ∈ P_m` iff `σ_β = id`.
- *Angle changes.* For a path `q = (q_1, …, q_m)` in `Conf_m(C)` and `i ≠ j`, let
  `A_{ij}(q) = θ(1) − θ(0)`, where `θ` is a continuous real lift of
  `arg(q_j(t) − q_i(t))`. Then `A_{ij} = A_{ji}`. It is additive under
  concatenation, changes sign under reversal, and is invariant under homotopy
  rel endpoints.
- *Winding numbers.* For `p ∈ P_m` let `lk_{ij}(p) = A_{ij}(p̃)/2π ∈ Z`. This is a
  homomorphism `P_m → Z`. Put `tot_k(p) = Σ_{j ≠ k} lk_{kj}(p)`.

### 4.2 Four elementary facts

**(W1) Conjugation permutes winding numbers.** Let `β ∈ B_m` with `σ = σ_β`,
and `p ∈ P_m`. Then `βpβ⁻¹ ∈ P_m`, `lk_{ij}(βpβ⁻¹) = lk_{σ(i)σ(j)}(p)` and
`tot_k(βpβ⁻¹) = tot_{σ(k)}(p)`.

*Proof.* Write `p̃ = (p_1, …, p_m)`. The lift of `p` starting at
`(σ(1), …, σ(m))` is `p̃^σ = (p_{σ(1)}, …, p_{σ(m)})`, a loop. So the lift of
`βpβ⁻¹` at `x_m` is `β̃ · p̃^σ · β̃^{rev}`, which is a loop. Its angle change for
`(i, j)` is `A_{ij}(β̃) + A_{σ(i)σ(j)}(p̃) − A_{ij}(β̃)`. Summing over `j ≠ k`
gives the last formula, since `σ` is a bijection. ∎

**(W2) Stabilization and forgetting.**
- *Stabilization.* Let `h : R → (−∞, m + 1/2)` be an increasing diffeomorphism
  equal to the identity on `(−∞, m]`, and `Φ(x + iy) = h(x) + iy`. For a loop
  `β` at `{1, …, m}` put `ι(β)(t) = Φ(β(t)) ∪ {m + 1}`. `Φ` is injective with
  `Re Φ < m + 1/2`, so this is a loop in `UConf_{m+1}(C)`. Homotopies are carried
  to homotopies, so `ι : B_m → B_{m+1}` is a well-defined homomorphism.
- *Forgetting.* Let `B_{m,1} = {β ∈ B_{m+1} : σ_β(m+1) = m+1}`. The space
  `UConf_{m,1}(C) = {(Z, w) : Z ∈ UConf_m(C), w ∈ C ∖ Z}` covers
  `UConf_{m+1}(C)` via `(Z, w) ↦ Z ∪ {w}`. A loop at `{1, …, m+1}` lifts to a
  loop at `({1, …, m}, m+1)` iff its strand from `m+1` returns to `m+1`. So
  `π_1(UConf_{m,1}(C), ({1, …, m}, m+1)) = B_{m,1}`, and `(Z, w) ↦ Z` induces a
  homomorphism `f : B_{m,1} → B_m`. Clearly `ι(B_m) ⊆ B_{m,1}`.

Properties:
- (a) `f∘ι = id`, so `ι` is injective. *Proof:* `f(ι(β)) = [Φ∘β]`. The maps
  `Φ_s(x + iy) = ((1−s)x + s h(x)) + iy` are injective and fix `1, …, m`, so
  `s ↦ Φ_s∘β` is a homotopy of loops at `{1, …, m}` from `β` to `Φ∘β`.
- (b) `ker f` is a free group. *Proof:* If `f(β) = 1`, then the strands from
  `1, …, m` return to their starting points, and so does the strand from
  `m + 1`. So `β ∈ P_{m+1}`. On `P_{m+1}`, `f` is induced by forgetting the last
  point, `Conf_{m+1}(C) → Conf_m(C)`. So `ker f` is the kernel in (FN), which is
  free.
- (c) For `b ∈ P_m` and `k ≤ m`, `lk_{k,m+1}(ι(b)) = 0`. *Proof:* the last
  coordinate is the constant `m + 1`, and `Re(Φ(b_k(t)) − (m+1)) < −1/2`, so the
  argument stays in `(π/2, 3π/2)`.

**(W3) The full twist.** Let `c_m = (m+1)/2`, and let `Δ²_m ∈ P_m` be the class
of the rigid rotation loop `R_m(t) = (c_m + e^{2πit}(k − c_m))_{k=1..m}`. (This
is the classical full twist, but only the properties below are used.)
- (a) *`Δ²_m` is central in `B_m`.* Let `β` be a loop at `{1, …, m}` and
  `ρ_s(z) = c_m + e^{2πis}(z − c_m)`. Define `T(s, t) = ρ_s(β(t))`, a map
  `[0,1]² → UConf_m(C)`. Its boundary, starting at `(0,0)`, runs `R_m` (edge
  `t = 0`), then `β` (edge `s = 1`), then `R_m` backwards, then `β` backwards.
  So `R_m β R_m⁻¹ β⁻¹ = 1` in `B_m`.
- (b) `lk_{ij}(Δ²_m) = 1` for all `i ≠ j ≤ m`, since
  `R_{m,j}(t) − R_{m,i}(t) = e^{2πit}(j − i)`. In particular `Δ²_m` has infinite
  order when `m ≥ 2`.
- (c) `R_m` stays in `{Re z ≤ m}`, where `Φ = id`. So `ι(Δ²_m)` is represented by
  `R_m` together with the constant point `m + 1`. Hence
  `lk_{ij}(ι(Δ²_m)) = 1` for `i ≠ j ≤ m`, and `lk_{k,m+1}(ι(Δ²_m)) = 0`.
- (d) `f(Δ²_{m+1}) = Δ²_m`. *Proof:* `f(R_{m+1})` is the rotation of `1, …, m`
  about `c_{m+1}`. Moving the centre linearly from `c_{m+1}` to `c_m` gives loops
  at `{1, …, m}` (every rotation is injective and fixes the set at `t = 0, 1`),
  hence a based homotopy to `R_m`.

**(W4) Free groups.** In a free group `F`, if `w` commutes with `δ ≠ 1` and some
homomorphism `Λ : F → Z` has `Λ(δ) = ±1`, then `w ∈ ⟨δ⟩`. *Proof:* by (NS),
`⟨w, δ⟩` is free abelian, hence `= ⟨u⟩` for some `u`. Write `δ = u^e`. Then
`eΛ(u) = ±1`, so `e = ±1` and `⟨u⟩ = ⟨δ⟩`. ∎

### 4.3 Proof of Proposition B

Let `n ≥ 2`, `γ = ι(Δ²_n)`, `z = Δ²_{n+1}` and `δ = γ⁻¹z`.

1. *Easy inclusion.* `z` is central in `B_{n+1}` (W3a), and `γ` is central in
   `ι(B_n)` (W3a and `ι` a homomorphism). So `⟨z⟩·ι(B_n) ⊆ C_{B_{n+1}}(γ)`.
2. *A centralizing braid fixes the last strand.* Let `β` commute with `γ` and
   `σ = σ_β`. By (W1), `tot_{n+1}(γ) = tot_{n+1}(βγβ⁻¹) = tot_{σ(n+1)}(γ)`. By
   (W3c), `tot_{n+1}(γ) = 0` and `tot_k(γ) = n − 1 ≥ 1` for `k ≤ n`. So
   `σ(n+1) = n+1` and `β ∈ B_{n,1}`.
3. *Peel off the first `n` strands.* Put `b = ι(f(β)) ∈ ι(B_n)` and `w = βb⁻¹`.
   Then `w ∈ B_{n,1}` and `f(w) = f(β)·f(ι(f(β)))⁻¹ = 1` by (W2a), so
   `w ∈ ker f`. `w` commutes with `γ`, because `β` does by hypothesis and `b` does
   by step 1.
4. *`w` is a power of `δ`.* `γ` and `z` are pure, and `f(z) = Δ²_n = f(γ)` by
   (W3d) and (W2a). So `δ ∈ ker f`. `w` commutes with `γ` and with the central
   `z`, hence with `δ`. Let `Λ = lk_{1,n+1}` restricted to `ker f ⊆ P_{n+1}`. By
   (W3b) and (W3c), `Λ(δ) = Λ(z) − Λ(γ) = 1 − 0 = 1`, so `δ ≠ 1`. `ker f` is free
   (W2b), so (W4) gives `w = δ^k` for some `k ∈ Z`.
5. *Conclusion.* `z` is central, so `δ^k = γ^{−k}z^k`. Hence
   `β = δ^k b = z^k·ι(Δ_n^{−2k} f(β)) ∈ ⟨z⟩·ι(B_n)`, where `Δ_n^{−2k}` means
   `(Δ²_n)^{−k}`. With step 1, `C_{B_{n+1}}(γ) = ⟨z⟩·ι(B_n)`.
6. *Direct product.* `z` is central, so multiplication
   `⟨z⟩ × ι(B_n) → C_{B_{n+1}}(γ)` is a surjective homomorphism. It is injective
   iff `⟨z⟩ ∩ ι(B_n) = 1`. Suppose `z^k = ι(b)`. Applying `f` and (W2a), (W3d)
   gives `b = (Δ²_n)^k ∈ P_n`, so `Λ(ι(b)) = 0` by (W2c). But `Λ(z^k) = k`, so
   `k = 0`. Finally `ι` is injective (W2a), and `z` has infinite order (W3b). ∎

*Check at `n = 2`.* `ι(Δ²_2) = σ_1²` in `B_3`, and the proposition says
`C_{B_3}(σ_1²) = ⟨σ_1⟩ × ⟨Δ²_3⟩ ≅ Z²`. This agrees with the mapping-class
picture: `σ_1²` is the Dehn twist about a curve around punctures `1, 2`. Its
centralizer is the stabilizer of that curve, which is generated by the half twist
inside it and the boundary twist. (Here `ι(σ_1) = σ_1` is the standard
stabilization; this identification is not used in the proof.)

## 5. Proof of Theorem M and corollaries

**Proof of Theorem M.**
- `n = 1`: `B_1` is trivial and acts geometrically on a point.
- `n ≥ 2`: suppose `B_{n+1}` acts geometrically on a complete CAT(0) space. By
  Proposition B, `C_{B_{n+1}}(ι(Δ²_n)) = ι(B_n) × ⟨Δ²_{n+1}⟩` with `Δ²_{n+1}` of
  infinite order. By Proposition G, `ι(B_n) ≅ B_n` acts geometrically on a
  complete CAT(0) space. ∎

**Corollary 5.1 (initial segment).** `S = {n ≥ 1 : B_n is CAT(0)}` satisfies
`n + 1 ∈ S ⇒ n ∈ S`. So `S` is either all of `Z_{≥1}` or `{1, …, N}` for some
`N`. With `braid-groups-on-at-most-six-strands-are-cat0`, `N ≥ 6`. Jeong
(arXiv:2009.09350, proof of Corollary 14; not imported into the graph) gives
`N ≥ 7`.

**Corollary 5.2 (reduction of the yes-direction).** Every braid group is CAT(0)
iff infinitely many braid groups are CAT(0).

*Proof.* If `S` is infinite, then for every `n` some `m ≥ n` lies in `S`, and
Corollary 5.1 gives `n ∈ S`. ∎

**Corollary 5.3 (shape of the no-direction).** Some braid group is not CAT(0)
iff there is `N` with `B_n` not CAT(0) for every `n > N`. So an obstruction
proved for one `B_{n_0}` propagates to all `B_n` with `n ≥ n_0`.

**Corollary 5.4 (quotients by the full twist).** If `B_n` is CAT(0) with
`n ≥ 2`, then `B_n/⟨Δ²_n⟩` and `P_n/⟨Δ²_n⟩` are CAT(0).

*Proof.* `Δ²_n` is central of infinite order in `B_n` (W3a, W3b), so
Proposition 3.1 gives `B_n/⟨Δ²_n⟩`. For `P_n`: a finite-index subgroup `P` of a
group acting geometrically acts geometrically. Properness restricts, and if
`G = ⋃_i P g_i` (finitely many cosets) and `GK = X`, then
`P·(⋃_i g_i K) = X`. `Δ²_n ∈ P_n` is central, so Proposition 3.1 applies again. ∎

(`⟨Δ²_n⟩` is the centre of `B_n` and of `P_n` by Chow's theorem, and
`P_n/Z(P_n) ≅ PMod(S_{0,n+1})`; neither fact is used.)

**What the argument does not give.**
- It gives no CAT(0) structure for any `n ≥ 8`. It only transfers structures
  downwards.
- It does not go upwards. `B_{n+1}` is not a centralizer in `B_n`, and a
  finite-index overgroup of a CAT(0) group need not be CAT(0) by any general
  principle known to us.
- It does not identify the downward space with the orthoscheme complex of
  `NCP_n`: `Y` is an abstract factor of a Min-set.

## 6. Checks, scope and novelty

**Sanity checks.**
- *Small cases.* `B_3 ⊇ C(σ_1²) = Z²` (§4.3). Proposition 3.1 on `Z²` acting on
  `E²` returns `Z` acting on `R`. For `n = 2`, Theorem M says `B_3` CAT(0) implies
  `B_2 = Z` CAT(0), which is true.
- *Computer check of Proposition B on finite balls.* The script is
  `experiments/braid-cat0-fewer-strands-2026-09-16/centralizer_check.py`, with
  output in `results.txt` in the same folder.
  - Braids are hashed through the faithful Artin action on `F_{n+1}`, which is
    independent of the configuration-space argument.
  - For `n = 2, 3, 4`, it checked every element of `B_{n+1}` of word length at
    most `12, 6, 5` that commutes with `(σ_1⋯σ_{n−1})^n`. All `79`, `579` and
    `1579` such elements fix the last strand and lie in
    `⟨(σ_1⋯σ_n)^{n+1}⟩·⟨σ_1, …, σ_{n−1}⟩`.
  - It found no `k ≠ 0` with `z^k` in the `B_n` ball.
  - This is a finite sanity check, not part of the proof.
- *Consistency with the literature.* Haettel–Kielak–Schwer (arXiv:1304.5990v2)
  prove `B_n` CAT(0) for `n ≤ 6`, and Jeong (arXiv:2009.09350v1) for `n ≤ 7`.
  Both prove, for each `n` in range, that the diagonal link of `|NCP_n|` is
  CAT(1) (HKS Theorem 4.17, Corollary 4.18; Jeong Corollary 14). Corollary 5.1 is
  consistent with both, since their sets of `n` are initial segments.
- *Where each hypothesis is used.*
  - Cocompactness of the `B_{n+1}`-action: Lemma 1.2 (properness of `X`),
    Lemma 1.3(a) (`Min ≠ ∅`) and the cocompactness in Proposition 2.1.
  - `n ≥ 2`: step 2 of §4.3 (`tot_k(γ) = n − 1 ≠ 0`).
  - Infinite order of `Δ²_{n+1}`: Lemma 1.3(c) (hyperbolicity).

**Scope of the inputs.** (BH1), (BH2) and (HR) are textbook CAT(0) geometry,
cited by number from Bridson–Haefliger (1999) and not re-read in this pass.
(BH2) is cited the same way by COMPLETE routes already in the graph. (FN) and
(NS) are classical. Everything braid-theoretic is proved from the configuration
space definitions.

**Novelty audit (2026-09-16).**
- The full texts of three primary sources were fetched and searched for any
  monotonicity-in-`n` statement or centralizer argument:
  - arXiv:1304.5990v2 (HKS);
  - arXiv:2009.09350v1 (Jeong);
  - arXiv:2411.18067v1 (Bregman–Libgober–Zhu, "CAT(0) geometry of complex curve
    complements and families", Nov 2024).
- None states Theorem M. HKS mention, as a general property of CAT(0) groups,
  that "the centralisers of infinite cyclic subgroups split". Bregman–Libgober–Zhu
  say CAT(0)-ness "is open even for finite type Artin groups such as braid groups
  B_n, n > 7".
- The ingredients are standard, so experts may well know the implication. We
  found it stated nowhere.
- What is new here:
  - the explicit abstract statement, for arbitrary geometric actions rather than
    for the Brady–McCammond complex;
  - a complete proof, including an elementary computation of
    `C_{B_{n+1}}(Δ²_n)`;
  - the resulting reductions, Corollaries 5.2–5.4.
