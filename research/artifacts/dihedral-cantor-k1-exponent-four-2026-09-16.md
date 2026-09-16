# Dihedral Cantor crossed products over F_2 have K_1 of exponent dividing 4

Agent: swarm-subshift-crossed-product-algeb, 2026-09-16. Supports the claims
`dihedral-cantor-crossed-product-k1-has-exponent-four` and `dihedral-sturmian-groupoid-algebra-is-no-subshift-ring`,
and settles decider (c) of `subshift-crossed-product-algebraic-cartans-are-conjugate` negatively.

## 0. Conventions

- Rings are unital. Modules are left modules. `GL_n(A)` acts on row vectors `A^n` by right multiplication, so its
  elements are left `A`-module automorphisms of `A^n`.
- `K_1(A) = GL(A)/[GL(A),GL(A)]`, and `[GL(A),GL(A)] = E(A)` (Whitehead lemma).
- Three textbook facts about `K_1` are used; each has a two-line proof, recalled here.
  - **(K-a) Conjugation.** `[gαg^(−1)] = [α]` for `g ∈ GL_n(A)`, because `K_1` is abelian.
  - **(K-b) Additivity.** Let `0 → P_1 → P → P_2 → 0` be an exact sequence of finitely generated free `A`-modules and
    `α_1, α, α_2` compatible automorphisms. Choose a splitting `P ≅ P_1 ⊕ P_2` and bases. Then `α` becomes the block
    matrix `[[α_1, 0],[β, α_2]]` (row-vector convention), which is `diag(α_1, α_2)` times an elementary matrix. Changing
    bases is conjugation, so by (K-a) `[α] = [α_1] + [α_2]`.
  - **(K-c) Morita.** `GL_k(M_n(A)) = GL_(kn)(A)`, and the stabilisations `k → k+1` form a cofinal subsystem of the
    stabilisations of `GL(A)`. Commutator subgroups correspond. So `K_1(M_n(A)) ≅ K_1(A)`.
- For a Cantor space `Y` and a group `Γ` acting by homeomorphisms, `LC(Y,F_2) ⋊ Γ = ⊕_(g∈Γ) LC(Y,F_2)δ_g` with
  `δ_g δ_h = δ_(gh)` and `δ_g f δ_g^(−1) = f∘g^(−1)`.

## 1. Lemma 1: an index-two normal extension doubles on K_1 over F_2

**Lemma 1.** Let `A` be an `F_2`-algebra, `A′ ⊆ A` a unital subring and `v ∈ A` a unit such that
`vA′v^(−1) = A′`, `v² ∈ A′` and `A = A′ ⊕ A′v`. Let `i_*: K_1(A′) → K_1(A)` be induced by the inclusion, and
`tr: K_1(A) → K_1(A′)` by restriction of scalars. Then `i_* ∘ tr = 2` on `K_1(A)`.

**Proof.**
- **Restriction is defined.** `A = A′·1 ⊕ A′·v` is a free left `A′`-module of rank 2, and since `A′v = vA′` it is
  also free of rank 2 as a right `A′`-module. So `A^n` restricted to `A′` is `A′^(2n)`, and a left `A`-linear
  automorphism `α` of `A^n` restricts to `tr(α) ∈ GL_(2n)(A′)`. This is a homomorphism compatible with stabilisation,
  so it induces `tr` on `K_1`.
- **The composite as a functor.** `i_*(tr(α))` is the matrix `tr(α)` read in `GL_(2n)(A)`. It is the automorphism
  `id ⊗ α` of `A ⊗_(A′) A^n = A ⊗_(A′) A′^(2n) = A^(2n)`. Also `A ⊗_(A′) A^n = (A ⊗_(A′) A) ⊗_A A^n`, and under this
  identification `id ⊗ α` is `id_(A⊗A) ⊗_A α`.
- **The bimodule sequence.** Let `μ: A ⊗_(A′) A → A` be multiplication, an `A`-bimodule map, and put
  `ω = 1⊗v + v⊗1`.
  - As a left `A`-module, `A ⊗_(A′) A = A(1⊗1) ⊕ A(1⊗v)`, because the right factor is free on `{1, v}` as a left
    `A′`-module.
  - `μ(a⊗1 + b⊗v) = a + bv`. Over `F_2` this vanishes iff `a = bv`, and then `a⊗1 + b⊗v = bv⊗1 + b⊗v = bω`.
    So `ker μ = Aω`, and `aω = av(1⊗1) + a(1⊗v)` is zero only for `a = 0`, so `a ↦ aω` is a left-linear bijection
    `A → ker μ`.
  - **Right action on `ω`.** Put `θ = Ad(v)`, `θ(b) = vbv^(−1)`, and `σ = θ|_(A′)`. For `c ∈ A′`:
    `1⊗vc = 1⊗σ(c)v = σ(c)⊗v` and `v⊗c = vc⊗1 = σ(c)v⊗1`, so `ωc = σ(c)ω`. For `v`, with `w = v² ∈ A′`:
    `ωv = 1⊗w + v⊗v = w⊗1 + v⊗v` and `vω = v⊗v + w⊗1`, so `ωv = vω = θ(v)ω`. Both sides of `ωb = θ(b)ω` are
    multiplicative in `b`, and `A′ ∪ {v}` generates `A`, so `ωb = θ(b)ω` for all `b ∈ A`.
  - So `ker μ ≅ A_θ`, the bimodule `A` with right action `x·b = xθ(b)`. The map `x ↦ xv` is a bimodule isomorphism
    `A_θ → A`: it is left linear, bijective, and `xθ(b)v = xvbv^(−1)v = (xv)b`.
  - `μ` has the right `A`-linear section `a ↦ 1⊗a`. So `0 → A → A ⊗_(A′) A → A → 0` is an exact sequence of
    `A`-bimodules that splits as right `A`-modules.
- **Conclusion.** Tensor over `A` with `A^n`. Right splitting keeps the sequence exact:
  `0 → A^n → A ⊗_(A′) A^n → A^n → 0`, of finitely generated free left `A`-modules. The automorphisms `id ⊗ α` on the
  three terms are compatible, and on both ends they are `α` (through the bimodule isomorphisms `ker μ ≅ A` and
  `μ`). By (K-b), `[i_*tr(α)] = [id ⊗ α] = [α] + [α]`. ∎

**Remarks.**
- Over a ring where `2 ≠ 0`, the same computation with `ω = 1⊗v − v⊗1` gives `ker μ ≅ A_(θ′)` with
  `θ′(v) = −v`, and the conclusion becomes `i_* tr(x) = x + θ′_*(x)`. Characteristic 2 is what makes the twist inner.
- Exact check of the identities `ωb = θ(b)ω` and `ker μ = Aω` on the finite crossed products `F_2^(Z/n) ⋊ D_n`,
  `n ∈ {3,4,5,6,8}`: `experiments/dihedral-cantor-k1-exponent-four-2026-09-16/bimodule_check.py`.

## 2. Theorem 2: K_1 of a dihedral Cantor crossed product has exponent dividing 4

**Setting.** `(Y,S)` is an infinite minimal Cantor system and `P: Y → Y` a homeomorphism with `P² = id` and
`PSP = S^(−1)`. Then `Γ = ⟨S, P⟩` is a quotient of `D_∞ = ⟨s_0, p_0 | p_0², p_0 s_0 p_0 = s_0^(−1)⟩`, and it is all
of `D_∞`: `S^k ≠ id` for `k ≠ 0` (no periodic points), and `S^k P ≠ id` for every `k` (else `P = S^(−k)`, and then
`S^(−1) = PSP = S`, so `S² = id`, impossible). Put `A = LC(Y,F_2) ⋊ D_∞` and
`A′ = ⊕_(k∈Z) LC(Y,F_2)δ_(S^k) = LC(Y,F_2) ⋊_S Z`.

**Theorem 2.** `4·K_1(A) = 0`.

**Proof.**
- **Lemma 1 applies** with `v = δ_P`. `D_∞ = ⟨S⟩ ⊔ ⟨S⟩P`, so `A = A′ ⊕ A′v`. `v² = δ_(P²) = 1`. And
  `v(fδ_(S^k))v^(−1) = (f∘P)δ_(S^(−k)) ∈ A′`. So `i_* ∘ tr = 2` on `K_1(A)`.
- **`K_1(A′)` is cyclic on `[u]`, `u = δ_S`.** `(Y,S)` is an infinite minimal Cantor system, so by
  `binary-subshift-ring-k1-is-half-orbit-index` the half-orbit index is an isomorphism `K_1(A′) → Z` with
  `ind(u) = −1`. Hence `K_1(A′) = Z·[u]`.
- **`i_*[u]` has order dividing 2.** `vuv^(−1) = δ_(PSP^(−1)) = δ_(S^(−1)) = u^(−1)`. By (K-a),
  `i_*[u] = [vuv^(−1)] = [u^(−1)] = −i_*[u]`.
- **Conclusion.** For `x ∈ K_1(A)`, `2x = i_*(tr x) ∈ i_*(K_1(A′)) = Z·i_*[u]`, which is killed by 2. So `4x = 0`. ∎

**Sanity check against known cases (not used in the proof).**
- One-point analogue. For `A = F_2[D_∞] ⊇ A′ = F_2[t^(±1)]` (the same index-two structure with `v` the reflection),
  Lemma 1 applies, and `K_1(F_2[t^(±1)]) = Z[t]` by Bass–Heller–Swan since `F_2` is regular. So the mechanism also gives
  `4·K_1(F_2[D_∞]) = 0`. A free-product formula for `K_1(F_2[Z/2] * F_2[Z/2])` would give an independent check, but
  Waldhausen Nil terms may intervene, and no source was fetched.
- Over a ring in which `2 ≠ 0`, the transfer gives `x + θ′_*(x)` in place of `2x` (§1 Remarks), where `θ′_*` is induced
  by the non-inner automorphism fixing `A′` and sending `v ↦ −v`. No torsion bound follows, so the argument is specific
  to characteristic 2. No claim is made about complex or C*-analogues.

## 3. Corollary 3: dihedral Cantor crossed products are not Morita equivalent to Z-crossed products

**Corollary 3.** In the setting of §2, let `(X,T)` be any infinite minimal Cantor system and
`R_X = LC(X,F_2) ⋊_T Z`. Then `M_m(A) ≇ M_n(R_X)` as rings, for all `m, n ≥ 1`.

**Proof.** A ring isomorphism induces an isomorphism on `K_1`. By (K-c), `K_1(M_m(A)) ≅ K_1(A)`, which has exponent
dividing 4 (Theorem 2). By (K-c) and `binary-subshift-ring-k1-is-half-orbit-index`, `K_1(M_n(R_X)) ≅ K_1(R_X) ≅ Z`,
which has an element of infinite order. ∎

**Reading.**
- `K_1 ≅ Z` of a Cantor minimal `Z`-crossed product records an orientation of the orbits. A `D_∞`-action with minimal
  rotation part `S` reverses that orientation through `P`, and over `F_2` the transfer turns the reversal into
  torsion.
- Corollary 3 needs no freeness or effectiveness. It applies equally when the `D_∞`-action is free, that is, when
  `P` and `SP` have no fixed points (every reflection `S^kP` is conjugate to one of them). Then `D_∞ ⋉ Y` is principal
  and minimal, and still not the transformation groupoid of an infinite minimal Cantor `Z`-system, since its algebra
  would otherwise be an `R_X`.

## 4. Corollary 4: the dihedral test object is not a subshift ring

**Setting (artifact `research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md` §5, generalised).**
- `(X,T)` is an infinite minimal Cantor system and `R: X → X` a homeomorphism with `R² = id`, `RTR = T^(−1)`.
- `X′ = X × Z/2`, `T′(x,e) = (Tx, e+1)`, `s(x,e) = (Rx, e+1)`.
- `s² = id`, and `sT′s(x,e) = sT′(Rx, e+1) = s(TRx, e) = (RTRx, e+1) = (T^(−1)x, e+1) = T′^(−1)(x,e)`. So `D_∞` acts,
  and `G_D = D_∞ ⋉ X′` is the dihedral groupoid of the cited §5.

**Lemma 4a.** If `T²` is minimal on `X`, then `T′` is minimal on `X′`.

**Proof.** Let `M ⊆ X′` be closed, nonempty, with `T′M = M`. Put `M_e = {x : (x,e) ∈ M}`, closed. `T′M = M` gives
`TM_0 = M_1` and `TM_1 = M_0`, so both are nonempty and `T²M_0 = M_0`. Minimality of `T²` gives `M_0 = X`, then
`M_1 = TX = X`, so `M = X′`. ∎

**Corollary 4.** If `T²` is minimal on `X`, then `A_(F_2)(G_D)` is not isomorphic to `M_n(R_Y)`, for any `n ≥ 1` and
any infinite minimal Cantor system `(Y, T_Y)`, in particular for any infinite minimal subshift `Y`.

**Proof.** `A_(F_2)(G_D) ≅ LC(X′,F_2) ⋊ D_∞` (`crossed-products-are-transformation-steinberg-algebras`). `X′` is a
Cantor space, and `(X′,T′)` is an infinite minimal system by Lemma 4a. So Corollary 3 applies with
`(Y,S,P) = (X′,T′,s)`. ∎

**Lemma 4b (Sturmian case).** Let `α ∈ (0,1)` be irrational, `x^θ_n = 1_([1−α,1))({θ + nα})` for `θ ∈ R`, and
`X_α` the closure of `{x^θ : θ ∈ R}` in `{0,1}^Z`, with `(Tx)_n = x_(n+1)` and `(Rx)_n = x_(−n)`. Then `(X_α,T)` is an
infinite minimal subshift on a Cantor space, `R(X_α) = X_α`, `R² = id`, `RTR = T^(−1)`, and `T²` is minimal on `X_α`.
The proof is self-contained (it does not quote the classical minimality of Sturmian subshifts).

**Proof.**
- **Shift and genericity.** `(Tx^θ)_n = x^θ_(n+1) = x^(θ+α)_n`, so `T^(±1)` preserve `X_α`. `x^θ` depends only on
  `θ mod 1`. Call `θ` generic if `θ ∉ Z + αZ`. For generic `θ` no `{θ + nα}` equals `0` or `1−α`, so for every `L`
  there is an open interval `J ∋ θ` on which `θ′ ↦ x^(θ′)|_([−L,L])` is constant.
- **Generic codings are dense.** Fix `θ` and `L`. For `t ∈ [0,1)` the indicator of `[1−α,1)` is constant on
  `[t, t+ε)` for small `ε > 0` (the interval is closed on the left and open on the right). So
  `x^(θ′)|_([−L,L]) = x^θ|_([−L,L])` for all `θ′ ∈ (θ, θ+ε)`, `ε` small, and this interval contains generic `θ′`. So
  `X_α` is the closure of the generic codings.
- **Generic cylinders.** For a word `w` on `[−L,L]` put `[w] = {x ∈ X_α : x|_([−L,L]) = w}`. Every nonempty open
  `U ⊆ X_α` contains a generic coding `x^(θ_1)`, hence contains `[w]` for `w = x^(θ_1)|_([−L,L])` and `L` large; and
  `{θ : x^θ ∈ [w]}` contains an open interval `J` by the first bullet.
- **Uniform recurrence, hence minimality of `T` and `T²`.** Let `r ∈ {1,2}` and `β = rα`, irrational. Fix `w`, `L`,
  `J` as in the previous bullet.
  - For every `θ` the forward orbit `{θ + kβ : k ≥ 0}` is dense in `R/Z`. So the open sets `J − kβ + Z`, `k ≥ 0`,
    cover `R`; by compactness of `R/Z` there is `K` with `R = ⋃_(k=0)^(K) (J − kβ + Z)`.
  - So for every `θ` some `k ∈ [0,K]` has `θ + kβ ∈ J + Z`, that is `T^(rk)x^θ = x^(θ+kβ) ∈ [w]`.
  - The property "`T^(rk)x ∈ [w]` for some `k ∈ [0,K]`" depends only on `x|_([−L, L+2K])`. Every finite window of a
    point of `X_α` is the same window of some `x^θ`. So every `x ∈ X_α` has `T^(rk)x ∈ [w]` for some `k ∈ [0,K]`.
  - Hence every forward `T^r`-orbit meets every nonempty open subset of `X_α`, and `T^r` is minimal, for `r = 1, 2`.
- **Infinite, Cantor.** Let `θ, θ′` be generic with `d = θ′ − θ ∉ Z`. Then `x^(θ′)_n = 1_(I−d)({θ + nα})` with
  `I = [1−α,1) ⊆ R/Z`. The arcs `I` and `I − d` are distinct half-open arcs of length `α ∈ (0,1)`, so their symmetric
  difference contains an open arc, which some `{θ + nα}` enters (density). So `x^θ ≠ x^(θ′)`, and `X_α` is
  uncountable. `X_α` is compact, metrizable and totally disconnected. If `x` were isolated, every orbit would meet the
  open set `{x}` (minimality), so `X_α` would be the single countable orbit of `x`; it is not. So `X_α` has no isolated
  points and is a Cantor space.
- **Reversal.** Fix generic `θ` and `n`, and put `t = {−θ + nα}`. Genericity gives `t ≠ 0` (else `θ ∈ nα + Z`) and
  `t ≠ α` (else `θ ∈ (n−1)α + Z`).
  - `(Rx^θ)_n = x^θ_(−n) = 1_I({θ − nα})`, and `{θ − nα} = 1 − t` because `t ≠ 0`. So `(Rx^θ)_n = 1` iff
    `1 − t ≥ 1 − α` iff `t ≤ α` iff `t ∈ (0, α)`.
  - `x^(1−α−θ)_n = 1_I({t + 1 − α})`. If `t ∈ (0,α)` then `t + 1 − α ∈ (1−α, 1)`, so the value is `1`. If
    `t ∈ (α,1)` then `{t + 1 − α} = t − α ∈ (0, 1−α)`, so the value is `0`.
  - So `Rx^θ = x^(1−α−θ)`, and `1−α−θ` is generic. `R` is continuous, `X_α` is closed and the generic codings are
    dense, so `R(X_α) ⊆ X_α`; with `R² = id` this gives `R(X_α) = X_α`. Finally
    `(RTRx)_n = (TRx)_(−n) = (Rx)_(−n+1) = x_(n−1) = (T^(−1)x)_n`. ∎

**Remark (other reflections).** For `j ∈ Z`, `R_j = T^jR` also satisfies `R_j² = T^jRT^jR = T^jT^(−j) = id` and
`R_jTR_j = T^(−1)`, and preserves `X_α`. Corollary 4 applies to each of them, so the choice of reflection centre in
the test object does not matter.

**Consequence.** For every irrational `α`, the dihedral Sturmian groupoid `G_D` of the cited §5 (with `R` the reversal
`(Rx)_n = x_(−n)`, or any `R_j`) satisfies the hypothesis of Corollary 4 by Lemma 4b. So
`A_(F_2)(G_D) = LC(X_α × Z/2, F_2) ⋊ D_∞` is isomorphic to no `R_Y` and to no matrix ring over one, for any infinite
minimal Cantor system `Y`. Decider (c) of `subshift-crossed-product-algebraic-cartans-are-conjugate` is settled
negatively: this test object refutes Cartan uniqueness at no `Y`. It also re-proves minimality of `T′`, which the cited
§5 derived from the absence of the eigenvalue `−1`.

## 5. The general orientation obstruction, and what remains for (D1)

**Proposition 5.** Let `G` be an ample Hausdorff groupoid, `H ⊆ G` a clopen subgroupoid with `H^(0) = G^(0)`, and
`B ⊆ G` a compact open bisection with `s(B) = r(B) = G^(0)`, such that `G = H ⊔ HB`, `BHB^(−1) = H` and `BB ⊆ H`.
Put `A = A_(F_2)(G) ⊇ A′ = A_(F_2)(H)`, `v = 1_B` and `θ = Ad(v)|_(A′)`. If `θ_* = −id` on `K_1(A′)`, then
`4·K_1(A) = 0`, and `A ≇ M_n(R_X)` for every infinite minimal Cantor system `X` and `n ≥ 1`.

**Proof.**
- **Lemma 1 applies.** For compact open bisections `U, V` one has `1_U * 1_V = 1_(UV)`. So `v·1_(B^(−1)) = 1_(r(B)) = 1`
  and `1_(B^(−1))·v = 1_(s(B)) = 1`: `v` is a unit. `vA′v^(−1)` consists of functions supported in `BHB^(−1) = H`, so
  it is `A′`. `v² = 1_(BB) ∈ A′`. `H` and `HB` are disjoint clopen sets covering `G`, so `A = A_(F_2)(H) ⊕ A_(F_2)(HB)`,
  and right convolution by `v` is a bijection `A_(F_2)(H) → A_(F_2)(HB)` with inverse right convolution by `1_(B^(−1))`
  (because `HBB^(−1) = H`, `B` being a bisection). So `A = A′ ⊕ A′v`, and `i_* ∘ tr = 2` on `K_1(A)`.
- **Conjugation.** Let `y ∈ K_1(A′)` be represented by `g ∈ GL_m(A′)`. In `GL_m(A)`,
  `diag(v,…,v)·g·diag(v,…,v)^(−1) = θ(g)` entrywise. By (K-a), `i_*(y) = i_*(θ_*y) = −i_*(y)`. So `2·i_*K_1(A′) = 0`.
- **Conclusion.** For `x ∈ K_1(A)`, `4x = 2·i_*(tr x) = 0`. The non-isomorphism follows as in Corollary 3. ∎

**Theorem 2 is the case** `G = D_∞ ⋉ Y`, `H = Z ⋉ Y`, `B = {P} × Y` (under `Ψ` of
`crossed-products-are-transformation-steinberg-algebras`, `v = δ_P`), where `K_1(A′) = Z[u]` and `θ_*[u] = −[u]`.

**Reading through the Giordano–Putnam–Skau index.** Suppose `H = Z ⋉ Y` for an infinite minimal Cantor system `(Y,S)`.
- Under `Ψ`, `Ψ(u^k χ_U) = 1_({k} × U)`, so for `γ ∈ [[S]]` with cocycle `n_γ` the unit `a_γ = Σ_k u^k χ_(\{n_γ = k\})`
  is `1_(C_γ)` with `C_γ = {(n_γ(y), y)}`. Every compact open bisection of `H` with full source and range is some
  `C_γ`.
- `θ(u) = 1_(B·C_S·B^(−1))`, and `B C_S B^(−1) ⊆ H` is such a bisection, so `θ(u) = a_(γ_B)` for a `γ_B ∈ [[S]]`.
- By `binary-subshift-ring-k1-is-half-orbit-index`, `ind(a_γ) = −I(γ)`, `ind(u) = −1` and `ind` is an isomorphism, so
  `[a_γ] = I(γ)[u]`. Hence `θ_* = I(γ_B) ∈ {±1}`.
- So Proposition 5 excludes, as Cartan models of any `M_n(R_X)`, all index-two extensions of a minimal `Z`-action
  groupoid by an orientation-reversing involutive bisection (`I(γ_B) = −1`).

**Remark (orientation-preserving commuting case; sketch, not used by any claim).** If `(Y,S)` is minimal and `P` is an
involution commuting with `S`, `P ≠ id`, then `Fix(P)` is closed, `S`-invariant and proper, hence empty. A free
involution of a Cantor space has a clopen fundamental domain `U`, `Y = U ⊔ PU`. Then `(Z × Z/2) ⋉ Y` is isomorphic to
the transformation groupoid of the two-step tower over `(Y/P, S̄)`. It is a `Z`-action groupoid, consistent with (D1),
and `K_1` gives no obstruction there.

**What remains open for (D1) and the target.**
- Cartan models of `R_X` whose isotropy or non-principal part does not come from a global index-two structure as in
  Proposition 5. Examples would be isotropy supported on a nowhere dense set without an involutive full bisection
  realising it, or an even part that is not a `Z`-action groupoid.
- Index-two extensions with `I(γ_B) = +1` where `P` does not commute with `S`.
- (D2), ring rigidity among subshifts, is untouched by this argument.
- Constraint on every Cartan model, from Proposition 5. Let `G` be an effective ample groupoid with
  `A_(F_2)(G) ≅ M_n(R_X)`. Then `G` admits no pair `(H, B)` as in Proposition 5 with `θ_* = −id` on
  `K_1(A_(F_2)(H))`, since otherwise `4·K_1(M_n(R_X)) = 0`, contradicting `K_1 ≅ Z`.
- A possible generalisation (§7 item 2 of the 2026-09-13 artifact). For an algebraic Cartan `B` of `R_X` with model
  `G_B`, the units `1_C` for full compact open bisections `C` of `G_B` give a homomorphism `[[G_B]] → GL_1(R_X)`.
  Composing with `ind` gives a homomorphism `[[G_B]] → Z`. Whether it always comes from a continuous fibre-bijective
  cocycle on `G_B` is open; a yes would prove (D1).
