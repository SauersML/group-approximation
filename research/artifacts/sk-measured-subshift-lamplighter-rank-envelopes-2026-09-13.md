# sk-measured-subshift: rank envelopes for sofic groups without a measured free minimal subshift

Lane `sk-measured-subshift`, 2026-09-13.

Brief: does every non-amenable sofic group admit a free minimal subshift with an invariant measure and
sofic-approximation labellings? That is the input of Theorem SR in
`research/artifacts/sk-sofic-embedding-b-ultraproduct-envelopes-2026-09-13.md` §4. Read Elek–Lippner at source.

## 0. Results

- **(A) The input is not needed for rank envelopes.** The lamplighter action of `L = Z/2 ≀ Δ` on `2^Δ` carries the
  Bernoulli measure. For every finitely generated infinite sofic `Δ`, the crossed product
  `R = LC(2^Δ, k) ⋊ L` has a faithful unital rank model, obtained by exact counting on `2^(V_k) × V_k` (Theorem A, §2).
- **(B) Every finitely generated sofic group is a subgroup of an infinite finitely generated simple Kazhdan
  `F_2`-linear sofic group** (Theorem B, §3). The route is: half-line overgroup, Theorem A, projective transfer,
  Whitehead embedding.
- **(C) The brief's question itself stays OPEN** (§4).
  - Elek 2021 gives free minimal actions with invariant measures, but over the infinite alphabet `𝒞 × ∏ F_m`.
  - Bernshteyn 2019 gives, for sofic `Γ`, free finite-alphabet subshifts with invariant measures and positive sofic
    entropy, but not minimal ones.
  - Kerr–Li's variational principle turns the labelling hypothesis into "the sofic topological entropy is not `−∞`".

All of this is unreviewed. Claims and routes are listed in §6.

## 1. Sources, quoted verbatim from the arXiv e-print TeX on MSI

**Elek–Lippner, *Sofic equivalence relations*, arXiv:0906.3619.** The journal data was not checked; the Crossref
query failed.
- Definition: "We say that the Borel action θ is *sofic* if there is a sequence of actions θ_n of 𝔽_∞ on finite
  X-sets Y_n such that for any r ≥ 1 and α ∈ U^{r,r} lim_{n→∞} p_α(θ_n) = p_α(θ)."
- Theorem (label `orbeqthm`): "If θ_1 is a sofic action and θ_2 is measured orbit equivalent to θ_1 then θ_2 is also
  sofic."
- §"The Bernoulli shift", Proposition: "The Bernoulli shift of a sofic group is sofic." The proof labels the vertices
  of a sofic approximation by a random function ω and uses ω_g(γ) = ω(g·w_γ), "for almost all ω's".

**Elek, *Free minimal actions of countable groups with invariant probability measures*.** Ergodic Theory Dynam.
Systems 41 (2021) 1369–1389, doi:10.1017/etds.2020.11 (Crossref), arXiv:1805.11149.
- Theorem 1: "For any countably infinite group Γ, there exists a free minimal continuous action α: Γ ↷ 𝒞 on the
  Cantor set admitting an invariant Borel probability measure."
- The alphabet: "From now on we use 𝓕 as a shorthand for 𝒞 × ∏_{m=1}^∞ F_m". Proposition `mainpropo`: "There exists
  a free and minimal Bernoulli subshift M ⊂ 𝓕^Γ …".
- So Elek's subshift is over an infinite compact alphabet. This is the result already imported on main as
  `elek-free-minimal-cantor-actions-with-invariant-measures`.

**Bernshteyn, arXiv:1802.07123.** The abstract matches Crossref's *Building large free subshifts using the Local
Lemma*, Groups Geom. Dyn. 13 (2019) 1417–1436, doi:10.4171/ggd/528.
- Theorem (label `theo:corl`): "Let U ⊆ k^Γ be a nonempty shift-invariant open set. Then, for any h < log_2 k:
  (i) there exists a free minimal subshift X ⊆ U of Hausdorff dimension at least h; (ii) if Γ is amenable, then there
  exists a free minimal subshift X ⊆ U of entropy at least h; (iii) if Γ is sofic, then there exists a free subshift
  X ⊆ U whose entropy with respect to any sofic approximation is at least h."
- Main theorem, item (iii): "there exist an invariant probability measure μ on X′ and a factor map
  π: ([0;1]^Γ, λ^Γ) → (X′, μ)."

**Kerr–Li, *Entropy and the variational principle for actions of sofic groups*, arXiv:1005.0399.**
- Theorem (label `T-variational`): "Let α be a continuous action of a sofic countable group G on a compact metrizable
  space X. Then h_Σ(X,G) = sup_{μ∈M_G(X)} h_{Σ,μ}(X,G). In particular, if h_Σ(X,G) ≠ −∞ then M_G(X) is nonempty."
- The published numbering (Invent. Math. 186 (2011)) was not checked.

## 2. Theorem A: rank models for lamplighter hosts over sofic groups

**Setup.**
- `Δ`: a finitely generated infinite sofic group, with finite symmetric generating set `S ∋ e`.
- `Z = 2^Δ`, with `(δx)(h) = x(δ^(-1)h)`. The map `a` flips the coordinate at `e`, and `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ`.
- `k`: any field. `R = LC(Z,k) ⋊ L = ⊕_(ℓ∈L) LC(Z,k) u_ℓ`, with `u_ℓ f u_ℓ^(-1) = f∘ℓ^(-1)`.
- `ν`: the uniform product measure on `Z`. It is `L`-invariant: `Δ` permutes coordinates and `a` flips one fair coin.

**Lemma 1.** `L ↷ Z` is minimal and topologically free, and `R` is finitely generated.
- *Minimal.* The flips generate `⊕_Δ Z/2`, which acts by finite modifications, so every orbit is dense.
- *Topologically free.* Write `ℓ = λδ` with `λ ∈ ⊕_Δ Z/2` and `δ ∈ Δ`, so `ℓx = λ + δx`.
  - If `δ = e` and `λ ≠ 0`, then `ℓ` has no fixed point.
  - If `δ ≠ e`, take a cylinder `[p]` on a finite window `W`. Since `Δ` is infinite, some `h` satisfies
    `h, δ^(-1)h ∉ W` and `h ∉ supp λ`. Choose `x ∈ [p]` with `x(h) ≠ x(δ^(-1)h)`. Then `ℓx ≠ x`, so `Fix(ℓ)` has empty
    interior.
- *Finitely generated.* Take `u_s` for `s ∈ S`, `u_a`, and `e_1 = 1_{x(e)=1}`. Conjugates `u_δ e_1 u_δ^(-1)` give
  every coordinate indicator, and products and complements of these give `LC(Z,k)`.

**The models.**
- A sofic approximation is given by maps `σ_k : Δ → Sym(V_k)` with `|V_k| → ∞`. For each finite `K ⊆ Δ`, the set of
  `K`-good `v` has density tending to 1. Here `v` is `K`-good if `σ_k(g)σ_k(h)v = σ_k(gh)v` for `g, h ∈ K` and
  `σ_k(g)v ≠ v` for `g ∈ K∖{e}`.
- Write `v·h = σ_k(h^(-1))v`. On `K`-good points this is a right action on products of elements of `K`, and
  `h ↦ v·h` is injective on `K`.
- `E_k = 2^(V_k) × V_k`, `N_k = |E_k|`, `W_k = k[E_k]`.
- For `p = (c,v)`, the partial configuration is `x_p(h) = c(v·h)`.
- Permutations of `E_k`: `π_k(s)(c,v) = (c, v·s^(-1))` for `s ∈ S`, and `π_k(a)(c,v) = (c + 1_v, v)`. For `ℓ ∈ L`,
  fix a word `w_ℓ` in `S ∪ {a}`; `π_k(ℓ)` is the product along `w_ℓ`, and `U_ℓ` is its permutation matrix.
- For `f ∈ LC(Z,k)` fix a finite window `B_f` with `f(x) = F_f(x|_(B_f))`, and let `D_k(f)e_p = F_f(x_p|_(B_f)) e_p`.
- `Φ_k(Σ_ℓ f_ℓ u_ℓ) = Σ_ℓ D_k(f_ℓ) U_ℓ`. This is linear and unital by definition.

**Localization.** Fix finite sets of windows and words, and a finite `K ⊆ Δ` containing all their partial products.
For `p = (c,v)` with `v` `K`-good:
1. `x_(π_k(ℓ)p) = ℓ·x_p` on the windows.
   - For `s ∈ S`: `x_(π(s)p)(h) = c((v·s^(-1))·h) = c(v·(s^(-1)h)) = (s·x_p)(h)`.
   - For `a`: `x_(π(a)p)(h) = c(v·h) + [v·h = v] = x_p(h) + [h = e]`, by freeness on `K`.
   - Induct along `w_ℓ`.
2. `π_k(ℓ)π_k(ℓ′)p = π_k(ℓℓ′)p`, because near `v` the permutations realize the relations of `L` restricted to the ball
   `K`.
3. For distinct `ℓ = λδ` in the finite set, the points `π_k(ℓ)p` are distinct:
   - distinct `δ` give distinct base points `v·δ^(-1)`;
   - equal `δ` with distinct `λ` give distinct colourings, since `h ↦ v·h` is injective on `K`.

**Theorem A.** For `r, s ∈ R`:
- (i) `Φ_k(r+s) = Φ_k(r) + Φ_k(s)` and `Φ_k(1) = I`;
- (ii) `rank(Φ_k(rs) − Φ_k(r)Φ_k(s)) = o(N_k)`;
- (iii) if `r ≠ 0`, then `rank Φ_k(r) ≥ ν(U) N_k − o(N_k)` for a nonempty clopen `U` depending only on `r`.

So `(Φ_k)` induces an injective unital homomorphism `R → ∏_ω M_(N_k)(k)/{rank-null}`.

*Proof of (ii).*
- `(fu_ℓ)(gu_(ℓ′)) = f(g∘ℓ^(-1))u_(ℓℓ′)`.
- On every column `e_q` whose base point is good, `U_ℓ D_k(g) U_ℓ^(-1) e_q = g(x_(π(ℓ)^(-1)q)) e_q = D_k(g∘ℓ^(-1)) e_q`,
  by item 1.
- On such columns `U_ℓ U_(ℓ′) = U_(ℓℓ′)`, by item 2.
- So `Φ_k(rs) − Φ_k(r)Φ_k(s)` vanishes on every column with a good base point. Its rank is at most
  `2^(|V_k|) · #{bad v} = o(N_k)`.

*Proof of (iii).*
- Let `r = Σ_(ℓ∈F) f_ℓ u_ℓ ≠ 0` and pick `ℓ_0` with `f_(ℓ_0) ≠ 0`.
- By Lemma 1 the set of points fixed by no element of `F^(-1)F∖{e}` is open and dense. So there is a nonempty clopen
  `U` such that `f_(ℓ_0)∘ℓ_0 ≡ λ ≠ 0` on `U` and `U ∩ ℓU = ∅` for `ℓ ∈ F^(-1)F∖{e}`.
- Let `C_k = {p = (c,v) : v good, x_p ∈ U}`.
  - For good `v`, the restriction `c ↦ x_(c,v)|_B` is uniform on `2^B`, so `#{c : x_(c,v) ∈ U} = ν(U)2^(|V_k|)`
    exactly.
  - Hence `|C_k| ≥ ν(U)N_k − o(N_k)`.
- `Φ_k(r)e_p = Σ_ℓ f_ℓ(x_(π(ℓ)p)) e_(π(ℓ)p)`. Suppose row `π(ℓ_0)p` has a nonzero entry in a column `p′ ∈ C_k`.
  - Then `π(ℓ)p′ = π(ℓ_0)p` for some `ℓ ∈ F`, so `ℓ·x_(p′) = ℓ_0·x_p` on the window.
  - So `x_p ∈ U ∩ ℓ_0^(-1)ℓU`, which forces `ℓ = ℓ_0`, and then `p′ = p`.
- The submatrix with rows `π(ℓ_0)C_k` and columns `C_k` is therefore `λI`.
- `ν(U) > 0` because `ν` has full support. ∎

No amenability and no subshift over `Δ` are used. The only dynamical inputs are the Bernoulli measure (exact counting)
and topological freeness (existence of `U`).

## 3. Theorem B

**Theorem B.** Let `Γ` be a finitely generated sofic group. Then `Γ` is a subgroup of an infinite, finitely generated,
simple group with property (T) that is `F_2`-linear sofic.

*Proof.*
1. **Overgroup.** `Δ = C(Γ)` is the half-line overgroup. It is finitely generated, infinite and sofic, and
   `δ_0 : Γ ↪ [Δ,Δ]` (`groups-embed-in-derived-subgroup-of-half-line-overgroup`). §5 gives an independent overgroup.
2. **Host.**
   - `L = Z/2 ≀ Δ` acts on `Z = 2^Δ`, and `R = LC(Z,F_2) ⋊ L`.
   - By Lemma 1 the action is minimal and topologically free, and `R` is finitely generated.
   - `R` is the Steinberg algebra of the transformation groupoid (`crossed-products-are-transformation-steinberg-algebras`).
     It is simple (`steinberg-algebra-simple-iff-minimal-effective`) with centre `F_2`
     (`minimal-effective-steinberg-algebras-have-scalar-centre`).
3. **The group.** `G = EL_3(R)`:
   - simple with trivial centre (`binary-el-simple-iff-minimal-topologically-free`);
   - Kazhdan (`elementary-groups-over-fg-rings-have-property-t`);
   - finitely generated and infinite, since `e_12(LC(Z,F_2))` is infinite.
4. **Linear soficity.** Theorem A with `k = F_2` gives a unital injective homomorphism into a rank ultraproduct. By
   `rank-modelled-simple-rings-give-linear-sofic-projective-el`, `G = G/Z` is `F_2`-linear sofic.
5. **Embedding.** `Δ ≤ L` gives `[Δ,Δ] ≤ [L,L]`. The map `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L]` in `EL_3(R)`
   (`perfect-groups-embed-in-crossed-product-elementary-groups`, item 3), and composing with `δ_0` embeds `Γ`. ∎

**Remarks.**
- It covers amenable inputs (`amenable-groups-embed-in-kazhdan-linear-sofic-via-half-line`) as a special case. The host
  replaces a free minimal subshift over `Δ` by the lamplighter action. That is exactly what removes the measured-subshift
  input for non-amenable `Δ`.
- It is the rank-metric half of `sofic-groups-embed-in-simple-kazhdan-sofic-groups`. The Hamming half is untouched,
  since `gap-sofic-approximations-are-local-embeddings` still applies to these models.
- Not an equivalence: subgroups of `F_2`-linear sofic groups are `F_2`-linear sofic, but "linear sofic implies sofic" is
  open (Arzhantseva–Păunescu).
- Over `F_q` the same construction gives `EL_3(R)/Z` simple (Steinberg criterion) and linear sofic. It is not claimed
  here.

## 4. The brief's question: status

**(a) Kerr–Li reduction.**
- Let `Y ⊆ A^Γ` be a subshift over a sofic `Γ` with sofic approximation `Σ`.
- If `h_Σ(Y) ≠ −∞`, some invariant `μ` has `h_(Σ,μ)(Y) ≠ −∞`. Its measure microstate spaces for the cylinder
  observables are then nonempty along a subsequence of `Σ`.
- These are the labellings of Theorem SR. So the question becomes whether a free minimal subshift `Y` with
  `h_Σ(Y) ≠ −∞` exists.

**(b) Bernshteyn 2019 (iii).**
- For sofic `Γ` it gives free subshifts with sofic entropy `≥ h > 0`, hence invariant measures with microstates.
- Minimality is claimed only for amenable `Γ` (item ii). A minimal subsystem of such an `X` is free and minimal, but it
  may be null for every invariant measure.

**(c) Elek 2021.**
- Free minimal with an invariant measure, over the alphabet `𝒞 × ∏ F_m`.
- A finite-alphabet factor keeps minimality but can lose freeness.
- The crossed product over an infinite-alphabet system is not finitely generated, so EJZ does not apply.

**(d) Status.** OPEN. The check is bounded: these four sources read at source, plus a grep of main. For rank envelopes
it is no longer needed (Theorem B).

## 5. Independent overgroup: metric ultraproducts and Ore

Let `Γ` be sofic and generated by a finite `S`.
- `Γ` embeds in `M = ∏_ω Sym(n_k)/{Hamming-null}`.
- Doubling `σ ↦ σ ⊕ σ` preserves the normalized Hamming distance and lands in `Alt(2n_k)`.
- For `s ∈ S` with image `(τ_k)`, Ore's Theorem 1 (`ore-even-permutations-are-commutators`) gives
  `τ_k = [a_k,b_k]` in `Sym(2n_k)`.
- Put `a_s = (a_k)` and `b_s = (b_k)`. Then `Δ′ = ⟨Γ, a_s, b_s : s ∈ S⟩` is a countable subgroup of a metric
  ultraproduct of symmetric groups, hence sofic, and `Γ ≤ [Δ′,Δ′]`.

This is a check on the gate from a second construction. It is not landed as a separate claim, so as not to duplicate
the half-line node.

## 6. Landed nodes and manuscript

- Claims (with routes):
  - `sofic-lamplighter-bernoulli-crossed-products-have-rank-models` (route `sofic-lamplighter-bernoulli-rank-models-proof`,
    `requires: []`, §2);
  - `sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups` (route
    `sofic-groups-simple-kazhdan-linear-sofic-envelope-proof`, §3).
- Attempts merged into:
  - `sofic-groups-have-measured-free-minimal-subshifts` (§4);
  - `sofic-groups-embed-in-simple-kazhdan-sofic-groups` (Theorem B).
- Manuscript: no proposal. The note's envelope corollary is LEF, and the linear-sofic envelope answers no printed
  question.
