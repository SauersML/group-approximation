---
rg: 2
id: bounded-defect-domain-dual-failure-proof
kind: route
title: Bound the defect components, lift by the repair lemma, and check that repairs and gluings never create or merge defects
target: strict-pairs-give-dual-failures-on-bounded-defect-domains
requires:
  - decoders-lift-changes-away-from-infinite-defect-chains
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

Notation as in the target. Automata use the convention `F(x)(g) = f((g⁻¹x)|_N)` with `(g⁻¹x)(w) = x(gw)`.
- Equivariance reads `F(g⁻¹x) = g⁻¹F(x)`.
- `τ(w)(g)` depends only on `w` on `gM`. `E(x)(g)` depends only on `x` on `gW`.
- `U = W⁻¹W` is symmetric and contains `W`, because `1 ∈ W`. So `U ⊇ M`, and adjacency is a symmetric relation.
- `Δ(a, b)` is the set of sites where `a` and `b` differ.

**0. Three facts used throughout.**
- **(F1) Center rule.** If `g ∉ D(x)`, then `E(x)(g) = x(g)`. This is part 3 of the repair lemma's proof in
  `decoder-defect-chain-repair-proof`: for `p ∈ L`, `ε(p) = p(1)`.
- **(F2) Legal windows.** `D(z) = ∅` for every `z ∈ Y`. Indeed `g⁻¹z ∈ Y`, since `Y` is shift-invariant, so
  `(g⁻¹z)|_W ∈ L`.
- **(F3) Small components are local.** Let `K` be a connected set of at most `R` sites that contains a site
  `k0`. Every `k ∈ K` is joined to `k0` by a path inside `K` with at most `R − 1` steps, each step a right
  multiplication by an element of `U`. So `K ⊆ k0U^{R−1}`.
- **(F4) Shift-invariance of defects.** `(g⁻¹(hx))|_W = ((h⁻¹g)⁻¹x)|_W`, so `D(hx) = hD(x)`. Left
  multiplication preserves adjacency, so `h` maps components of `D(x)` onto components of `D(hx)`.

**1a. `X_R` is a subshift of finite type.**
- **Shift-invariant.** This follows from (F4).
- **Forbidden patterns.** Let `𝒬` be the family of connected sets `Q ∋ 1` with `|Q| = R + 1`. By (F3),
  `Q ⊆ U^R`, so `𝒬` is finite.
- **Characterization.** A component of `D(x)` has more than `R` elements iff it contains a connected subset of
  exactly `R + 1` elements (grow a breadth-first tree inside it). So `x ∉ X_R` iff `gQ ⊆ D(x)` for some
  `g ∈ G` and `Q ∈ 𝒬`.
- **Locality.** By (F4), `gQ ⊆ D(x)` iff `Q ⊆ D(g⁻¹x)`. That depends only on `(g⁻¹x)|_{QW}`.
- **Conclusion.** `X_R` is defined by the finite set of forbidden patterns
  `{p ∈ A^{QW} : for every q ∈ Q, the window (q⁻¹p)|_W is not in L}`, `Q ∈ 𝒬`. Here `(q⁻¹p)(w) = p(qw)`.

**1b. `Y ⊆ X_R`.** This follows from (F2).

**3. Surjectivity with a section.** `τ` maps `A^G` into `Y ⊆ X_R`, and `σ(τ(w)) = w`.

**2. Strong post-surjectivity, with `Φ = M⁻¹U^R` and lifts inside `X_R`.** Let `x ∈ X_R` and `z ~ σ(x)`.
Put `S = Δ(σ(x), z)`, which is finite.
- **Target in the image.** Put `y = τ(z) ∈ Y`. Let `F = Δ(E(x), y) = Δ(τσ(x), τ(z))`.
  - If `g ∈ F`, then `σ(x)` and `z` differ somewhere on `gM`, so `g ∈ SM⁻¹`. Thus `F ⊆ SM⁻¹` is finite.
- **The overwritten set is small.** Let `C` be the union of the components of `D(x) ∪ F` that meet `F`. We
  claim `C ⊆ FU^R`. Take `h` in such a component, with a path `f = h_0, h_1, …, h_n = h` inside `D(x) ∪ F`
  starting at `f ∈ F`.
  - If `h ∈ F`, we are done, because `1 ∈ U^R`.
  - Otherwise let `h_j` be the last site of the path in `F`. The sites `h_{j+1}, …, h_n` lie in `D(x)` and
    form a path, so they lie in one component `K` of `D(x)`. Also `h_{j+1} ∈ h_jU ⊆ FU`.
  - `x ∈ X_R` gives `|K| ≤ R`. So by (F3), `h ∈ h_{j+1}U^{R−1} ⊆ FU^R`.
- **Repair.** Since `C` is finite, the repair lemma (part 3 of
  `decoders-lift-changes-away-from-infinite-defect-chains`) applies. It says that `x'`, equal to `y` on `C`
  and to `x` off `C`, satisfies `E(x') = y`.
  - So `τ(σ(x')) = τ(z)`, and injectivity of `τ` gives `σ(x') = z`.
  - Moreover `Δ(x, x') ⊆ C ⊆ FU^R ⊆ SM⁻¹U^R = Δ(σ(x), z)Φ`.
- **The lift stays in `X_R`.** The proof of the repair lemma (`decoder-defect-chain-repair-proof`, part 3)
  shows two things.
  - For `g ∈ CW⁻¹`, the window `(g⁻¹x')|_W` equals `(g⁻¹y)|_W`, which lies in `L`.
  - For `g ∉ CW⁻¹`, it equals `(g⁻¹x)|_W`.
  - Hence `D(x') = D(x) \ CW⁻¹ ⊆ D(x)`. Every connected subset of `D(x')` is a connected subset of `D(x)`,
    so every component of `D(x')` lies in a component of `D(x)` and has at most `R` elements. Thus
    `x' ∈ X_R`.

**4. Non-pre-injectivity when `R ≥ |P||W|`.** Fix `y0 ∈ Y`, and let `x1` equal `p` on `P` and `y0` off `P`.
- **`x1 ∈ X_R \ Y`.** If `gW ∩ P = ∅`, the window of `x1` at `g` is a window of `y0`, which is legal by (F2).
  So `D(x1) ⊆ PW⁻¹`, and every component has at most `|P||W| ≤ R` elements. Moreover `x1 ∉ Y`, because
  `x1|_P = p`.
- **A second point with the same image.** Put `x2 = E(x1) ∈ Y ⊆ X_R`.
  - By (F1), `x2 = x1` off `D(x1)`, so `x2 ~ x1`.
  - `x2 ≠ x1`, since `x2 ∈ Y` and `x1 ∉ Y`.
  - `σ(x2) = στσ(x1) = σ(x1)`.
- **Conclusion.** `x1` and `x2` are distinct asymptotic points of `X_R` with the same image.

**5. Properness when `W ⊇ PP⁻¹P`.**
- **A dense packing.** By Zorn's lemma, choose `H ⊆ G` maximal such that the sets `hP`, `h ∈ H`, are
  pairwise disjoint.
  - For every `g ∈ G`, maximality gives `h ∈ H` with `gP ∩ hP ≠ ∅` (take `h = g` if `g ∈ H`).
  - Then `h ∈ gPP⁻¹`, so `hP ⊆ gPP⁻¹P ⊆ gW`.
- **Every window is a defect.** Let `x(hq) = p(q)` for `h ∈ H` and `q ∈ P`, and let `x` be arbitrary
  elsewhere. Fix `g`, and take `h` as above; put `k = g⁻¹h`, so `kP ⊆ W`.
  - Suppose `(g⁻¹x)|_W = z|_W` for some `z ∈ Y`.
  - Then for `q ∈ P`, `(k⁻¹z)(q) = z(kq) = (g⁻¹x)(kq) = x(hq) = p(q)`.
  - So `k⁻¹z ∈ Y` restricts to `p` on `P`, which is impossible. Hence `D(x) = G`.
- **The single component is infinite.** The components of `G` under adjacency are the left cosets of `⟨U⟩`,
  and `⟨U⟩ ⊇ ⟨M⟩`. Suppose `H0 = ⟨M⟩` were finite.
  - For each left coset `c = gH0`, `τ(w)|_c` depends only on `w|_c`, because `chM ⊆ c`. So `τ` is the product
    over cosets of maps `τ_c : A^c → A^c`.
  - Each `τ_c` is injective. If `τ_c(a) = τ_c(b)`, extend `a` and `b` by a common configuration off `c`. The
    extensions have the same image, so `a = b` by injectivity of `τ`.
  - `A^c` is finite, so each `τ_c` is bijective. Then `τ` is bijective, contradicting strictness.
  - So `⟨M⟩`, and hence every component of `D(x)`, is infinite. Thus `x ∉ X_R` for every `R`.

**1c. `X_R` is strongly irreducible.** Put `T = W⁻¹UW ∪ UMM⁻¹U` and `Δ = U^R T U^R`.
- **Shape of `Δ`.** `T ⊇ U`, because `1 ∈ W`. `T` is symmetric, and so is `Δ`. Also `1 ∈ Δ`.
- **Setup.** Let `x1, x2 ∈ X_R`, and let `Ω1, Ω2` be finite with `Ω1Δ ∩ Ω2 = ∅`. For `i = 1, 2`:
  - let `C_i` be `Ω_i` together with the components of `D(x_i)` that meet `Ω_iU`;
  - put `K_i = C_iU \ C_i` and `y_i = E(x_i) ∈ Y`.
- **Size.** `C_i ⊆ Ω_iU^R`, by (F3) applied to each added component, which has at most `R` elements and meets
  `Ω_iU`.
- **Separation.** If `C1T ∩ C2 ≠ ∅`, then `Ω1U^R T ∩ Ω2U^R ≠ ∅`, so `Ω1Δ ∩ Ω2 ≠ ∅`, because `U^R` is
  symmetric. Hence `C1T ∩ C2 = ∅`, and symmetrically `C2T ∩ C1 = ∅`. Three consequences follow.
  - **(S1)** `C1U ∩ C2 = ∅ = C2U ∩ C1`, since `T ⊇ U`. Equivalently `C1W⁻¹ ∩ C2W⁻¹ = ∅`: if
    `c1w1⁻¹ = c2w2⁻¹`, then `c2 = c1w1⁻¹w2 ∈ C1U`.
  - **(S2)** No site of `C1W⁻¹` is adjacent to a site of `C2W⁻¹`. If `c2w2⁻¹ = c1w1⁻¹u`, then
    `c2 ∈ C1W⁻¹UW ⊆ C1T`.
  - **(S3)** `C1UM ∩ C2UM = ∅`. If `c1u1m1 = c2u2m2`, then `c2 ∈ C1UMM⁻¹U⁻¹ = C1UMM⁻¹U ⊆ C1T`.
- **Clean collars.** `K_i ∩ D(x_i) = ∅`. Take `h = cu ∈ K_i` with `c ∈ C_i` and `u ∈ U`.
  - If `c ∈ Ω_i`, then `h ∈ Ω_iU`, so if `h ∈ D(x_i)` its component was added to `C_i`.
  - If `c` lies in an added component, then `h`, adjacent to `c`, would lie in the same component if
    `h ∈ D(x_i)`.
  - Either way `h ∈ C_i`, contradicting `h ∈ K_i`. By (F1), `x_i = y_i` on `K_i`.
- **A common image background.** By (S3), there is `w ∈ A^G` with `w = σ(x_i)` on `C_iUM` for `i = 1, 2`. Put
  `y = τ(w) ∈ Y`.
  - For `g ∈ C_iU`, `y(g)` depends only on `w` on `gM ⊆ C_iUM`. So `y(g) = τ(σ(x_i))(g) = y_i(g)`.
  - Thus `y = y_i` on `C_iU`.
- **The glued point.** Let `x = x_i` on `C_i` (`i = 1, 2`) and `x = y` elsewhere. This is well defined by (S1).
  - **Agreement on `C_iU`.** On `K_i`, which misses `C_i` and, by (S1), also `C_j`, we have
    `x = y = y_i = x_i`. So `x = x_i` on `C_iU`, and in particular on `Ω_i ⊆ C_i`.
  - **Windows.** For `g ∈ C_iW⁻¹`, `gW ⊆ C_iU`, so the window of `x` at `g` is the window of `x_i` at `g`. For
    `g ∉ C1W⁻¹ ∪ C2W⁻¹`, `gW` misses `C1 ∪ C2`, so the window of `x` at `g` is a window of `y`, which is legal
    by (F2).
  - **Defect set.** Hence `D(x) = (D(x1) ∩ C1W⁻¹) ∪ (D(x2) ∩ C2W⁻¹)`.
  - **Components.** By (S2), the two parts are not adjacent to each other. So every component of `D(x)` is a
    connected subset of one `D(x_i)`, lies in a component of `D(x_i)`, and has at most `R` elements.
  - So `x ∈ X_R`, and `x` agrees with `x_i` on `Ω_i`.
- **Nonempty.** `X_R ⊇ Y ≠ ∅`. Hence `X_R` is strongly irreducible, with constant `Δ`.

**Assembly.** Parts 1a, 1b and 1c give item 1 of the target; parts 2, 3, 4 and 5 give items 2 to 5.
- **All five at once.** A memory of an automaton may be enlarged. So take `W = {1} ∪ M ∪ PP⁻¹P ∪ W_E`, with
  `W_E` a memory of `E`, and take `R ≥ |P||W|`.
- **Corollary.** Let `G` carry a strict pair. Then `X_R` is a proper strongly irreducible SFT, and
  `σ|_{X_R}` is strongly post-surjective and not pre-injective.
- **From non-surjunctivity to strict pairs.** Every injective, non-surjective automaton `τ` has a decoder.
  - `τ` is a continuous bijection from the compact space `A^G` onto the Hausdorff space `Y`, so `τ⁻¹ : Y → A^G`
    is continuous and equivariant.
  - The map `y ↦ τ⁻¹(y)(1)` is locally constant on the compact space `Y`, so it depends only on `y|_N` for a
    finite `N`.
  - Define `ν(q) = τ⁻¹(y)(1)` if `q = y|_N` with `y ∈ Y`, and `ν(q) = a0` otherwise. Put
    `σ(x)(g) = ν((g⁻¹x)|_N)`.
  - Then `σ(τ(w))(g) = ν(τ(g⁻¹w)|_N) = (g⁻¹w)(1) = w(g)`.
- **Conclusion.** Every non-surjunctive group carries a strict pair, and so fails
  `proper-sft-domains-admit-no-dual-failures`.
