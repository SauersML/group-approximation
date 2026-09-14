# sk-universal-lef-host-a: one simple Kazhdan LEF group for every countable family of LEF groups

Lane sk-universal-lef-host-a, 2026-09-13.
- Status: every result below has a complete proof here, and is UNREVIEWED. Review is requested in `sk/queue/sk-verify-7.txt`.
- **Priority.** Peer lane sk-universal-lef-host-b landed Lemma A and Theorem B first, at a303f6663a (20:18 CDT), as:
  - `countable-lef-groups-embed-in-two-generator-lef-groups`;
  - `countable-lef-groups-embed-in-simple-kazhdan-lef-groups`;
  - `simple-kazhdan-lef-host-for-recursive-lef-groups`;
  - `no-countable-group-contains-all-fg-lef-groups`.

  Main's graph uses THOSE nodes. §1–§2 below are an independent second derivation (wreath products `Sym(m)≀Z/2^(2n+3)`, positions `2^j`), which counts as a concurrence for review.
- **New in this lane:**
  - `simple-kazhdan-lef-host-iff-lef-and-countably-many-types` (Proposition D, the exact characterization);
  - the sentence "each `ι(γ_j)` is a commutator, so `ι(Γ) ≤ [Δ,Δ]`", merged onto the peer's Lemma A claim;
  - two routes that establish the Wilson-based claims `universal-simple-kazhdan-lef-groups-exist` and `simple-kazhdan-lef-host-for-countably-many-rf-groups` without Wilson;
  - the route `lef-groups-embed-via-two-generator-lef-envelope` into `lef-groups-embed-in-simple-kazhdan-lef-groups`, which needs no quotient doubling.

## 0. Results
- **Lemma A** (a finite Neumann–Neumann words lemma). For every countable LEF group `G = {g_1, g_2, …}` there is a 2-generator LEF group `Δ = ⟨a,b⟩` and an injective homomorphism `ι: G → Δ` with
  `ι(g_i) = [a^(−2^(2i−1)) b a^(2^(2i−1)), a^(−2^(2i)) b a^(2^(2i))]` for all `i`.
  So `ι(G) ≤ [Δ,Δ]`. The words do not depend on `G`.
- **Theorem B** (universal host). For every countable set `𝒞` of countable LEF groups, one infinite, finitely generated, simple group with property (T) that is LEF contains a copy of every member of `𝒞`.
- **Corollary C.** One such group contains:
  - every finitely generated LEF group with solvable word problem, and more generally every recursively presented one;
  - every finitely generated linear group and every finitely presented residually finite group;
  - every `G_X = EL_3(LC(X,F_2)⋊Z)` with `X` computable, and every derived topological full group `[[T]]'` of a computable minimal subshift (both are non-RF);
  - Hall's universal countable locally finite group, hence every countable locally finite group.
- **Proposition D** (sharp). For a set `𝒞` of finitely generated groups the following are equivalent:
  1. some infinite finitely generated simple Kazhdan LEF group contains every member of `𝒞`;
  2. some countable LEF group contains every member of `𝒞`;
  3. every member of `𝒞` is LEF, and `𝒞` has at most countably many isomorphism types.

  No group of type (1) contains all finitely generated LEF groups, because there are continuum many up to isomorphism.

## 1. Lemma A
**Conventions.**
- For a finite group `Q` and `N ≥ 1` let `W(Q,N) = Q^(Z/N) ⋊ ⟨t⟩`, with `t` of order `N` and `(t f t^(−1))(k) = f(k−1)`. So `(t^(−s) f t^s)(k) = f(k+s)`. The base is a direct product, so commutators of base elements are computed coordinatewise.
- `s_j = 2^j` for `j ≥ 1`. If `2^α − 2^β = 2^γ − 2^δ` with `α ≠ β`, then `2^α + 2^δ = 2^γ + 2^β`, so `{α,δ} = {γ,β}`. The case `α = β` is excluded, so `α = γ` and `β = δ`: differences of distinct powers of 2 are pairwise distinct.

**Proof.**
1. *Models.* Since `G` is LEF, for each `n` there is an injective map `φ_n` from `F_n = {g_1,…,g_n}` into a finite group `K_n` with `φ_n(gh) = φ_n(g)φ_n(h)` whenever `g, h, gh ∈ F_n`.
   - Compose with the left regular representation `K_n → Sym(K_n)`.
   - Then compose with the injective homomorphism `Sym(k) → Alt(k+2)`, `σ ↦ σ τ^(ε(σ))`, where `τ` swaps the two new points and `ε(σ) ∈ {0,1}` is the parity of `σ`.

   So we may take `φ_n` with values in `Alt(m_n) ≤ Sym(m_n)`, `m_n ≥ 5`.
2. *Ore witnesses.* By Ore's Theorem 1 (`ore-even-permutations-are-commutators`), choose `x_{i,n}, y_{i,n} ∈ Sym(m_n)` with `[x_{i,n}, y_{i,n}] = φ_n(g_i)` for `i ≤ n`.
3. *Finite wreath products.* Put `N_n = 2^(2n+3)`, `W_n = W(Sym(m_n), N_n)` and `a_n = t`. Let `b_n` be the base element with `b_n(s_(2i−1)) = x_{i,n}` and `b_n(s_(2i)) = y_{i,n}` for `i ≤ n`, and `b_n(k) = 1` otherwise. The positions `s_1, …, s_(2n) ≤ 2^(2n)` are distinct modulo `N_n`.
4. *Claim.* For `i ≤ n`, let `c = a_n^(−s_(2i−1)) b_n a_n^(s_(2i−1))` and `d = a_n^(−s_(2i)) b_n a_n^(s_(2i))`. Then `[c,d]` is the base element with value `φ_n(g_i)` at the coordinate `0` and `1` elsewhere.
   - `c(k) = b_n(k + s_(2i−1))` and `d(k) = b_n(k + s_(2i))`.
   - If both are `≠ 1`, then `k + s_(2i−1) ≡ s_α` and `k + s_(2i) ≡ s_β` modulo `N_n`, for some `α, β ≤ 2n`. So `s_α − s_β ≡ s_(2i−1) − s_(2i)`.
   - Both sides have absolute value at most `2^(2n)`, and their difference is below `N_n`, so they are equal integers. The right side is nonzero, so `α ≠ β`, and by distinct differences `(α,β) = (2i−1, 2i)` and `k ≡ 0`.
   - Coordinatewise, `[c,d](k) = [c(k), d(k)] = 1` for `k ≢ 0`, and `[c,d](0) = [x_{i,n}, y_{i,n}] = φ_n(g_i)`.
5. *Ultraproduct.* Let `ω` be a nonprincipal ultrafilter on `N` and `𝒲 = ∏_ω W_n` the algebraic ultraproduct: the product modulo sequences that equal `1` on an `ω`-large set. Put `a = [(a_n)]`, `b = [(b_n)]`, `Δ = ⟨a,b⟩`, and `ι(g) = [(ι_n φ_n(g))]`, where `ι_n` places an element at the coordinate `0`. When `g ∉ F_n` any value will do.
   - *Homomorphism.* For `g, h ∈ G` the set of `n` with `g, h, gh ∈ F_n` is cofinite.
   - *Injective.* If `g ≠ h`, then `φ_n(g) ≠ φ_n(h)` for cofinitely many `n`.
   - *Words.* By the claim, `ι(g_i) = [a^(−s_(2i−1)) b a^(s_(2i−1)), a^(−s_(2i)) b a^(s_(2i))]`, since the equality holds at every `n ≥ i`. So `ι(G) ≤ [Δ,Δ]`.
   - *LEF.* Every countable subgroup of an algebraic ultraproduct of finite groups is LEF. For finite `E ⊆ Δ` choose representatives `(e_n)`. The finitely many identities `e e' = e''` and inequalities `e ≠ e'` that hold among elements of `E` hold on an `ω`-large set of `n`. For such an `n`, `e ↦ e_n` is injective on `E` and preserves the products that stay in `E`.
   - `Δ` is infinite when `G` is. □

**Remarks.**
- *Credit.* The words and the sparse positions are the Neumann–Neumann wreath-product method (B. H. Neumann and H. Neumann, *Embedding theorems for groups*, J. London Math. Soc. s1-34 (1959), no. 4, 465–479, doi 10.1112/jlms/s1-34.4.465; metadata confirmed on Crossref; the paper itself not read by this lane; exposition checked at jaywillmath, 2013-08-16). Their version uses the unrestricted wreath product and positions `2^i − 1`. Here it is run in finite wreath products and passed through an ultraproduct, which is what keeps LEF. Wilson's residually finite analog (Math. Z. 174 (1980), Theorem A) is harder, because residual finiteness is not a local property.
- *Model tests.*
  - `G = BS(2,3)`: finitely presented and not residually finite, hence not LEF. There are no models `φ_n`, and indeed no LEF overgroup exists.
  - Finite `G`: the lemma holds trivially, and `Δ` may be finite.
  - `G = ⊕_n Alt(n)`: countable, locally finite and LEF. The construction applies directly.
- *Firewall.* Neither `x ↦ diag(x, x^(−1), 1)` nor `γ ↦ (γ, γ^(−1))` is a homomorphism on noncommuting elements. The lemma uses neither: `ι_n` is insertion at one coordinate, which is a homomorphism.

## 2. Theorem B
Let `𝒞 = {Γ_1, Γ_2, …}`, each `Γ_j` countable and LEF.
1. *Direct sum.* `D = Z ⊕ ⊕_j Γ_j` (restricted sum) is countable and infinite. It is LEF:
   - a finite `E ⊆ D` lies in `Z × Γ_1 × … × Γ_k` for some `k`;
   - take partial models of the coordinate projections `E_j` and the product map;
   - it is injective, because elements are determined by their coordinates;
   - products `e e' = e''` inside `E` are coordinatewise products inside the `E_j`.
2. *Envelope.* By Lemma A, `D ≅ ι(D) ≤ [Δ,Δ]` for an infinite 2-generator LEF group `Δ`.
3. *Host.* Let `L = Z/2 ≀ Δ` act on `2^Δ` (shifts, and the flip at `e`), `R = LC(2^Δ,F_2) ⋊ L` and `U = EL_3(R)`. By `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` (three PASSes on main), `U` is infinite, finitely generated, simple, Kazhdan and LEF, and `ℓ ↦ diag(u_ℓ,1,1)` embeds `[L,L]` in `U`.
   - Why `[L,L]` lands in `EL_3`: `diag(x,x^(−1),1) ∈ E_3` by Whitehead. For units `x, y`, `diag(x,x^(−1),1)·diag(y,y^(−1),1)·diag((yx)^(−1), yx, 1) = diag(xyx^(−1)y^(−1), 1, 1)`: the first entry is `x y x^(−1) y^(−1)`, the second is `x^(−1) y^(−1) y x = 1`. And `ℓ ↦ diag(u_ℓ,1,1)` is an injective homomorphism `L → GL_3(R)`.
4. *Conclusion.* `Δ ≤ L`, so `[Δ,Δ] ≤ [L,L]`. Hence `U` contains `ι(D)`, and with it a copy of every `Γ_j`. □

## 3. Corollary C
Let `𝒞_0` be the union of the following classes, taken up to isomorphism:
- (i) finitely generated LEF groups with solvable word problem;
- (ii) recursively presented finitely generated LEF groups. Class (i) lies in (ii), since a solvable word problem gives a recursive relator set;
- (iii) finitely generated linear groups over fields. They are residually finite (Mal'cev), hence LEF;
- (iv) finitely presented residually finite groups; they lie in (ii);
- (v) `G_X` for computable infinite minimal subshifts `X`. These are LEF with `WP(G_X) ≡_T L(X)` (the note's corollary), so they lie in (i);
- (vi) `[[T]]'` for computable minimal subshifts. These are LEF (Grigorchuk–Medynets 2014, Theorem 2.6) with decidable word problem (Grigorchuk–Medynets 2018, Theorem 1.1(3)), so they lie in (i);
- (vii) Hall's universal countable locally finite group (P. Hall, J. London Math. Soc. 34 (1959) 305–319; recalled, not re-read). It is locally finite, hence LEF, and contains every countable locally finite group.

*Countability.*
- On finitely many generators there are countably many recursively enumerable relator sets, so (ii) is countable.
- For (iii): finitely many matrices lie over the finitely generated field their entries generate. Finitely generated fields have countably many isomorphism types, and each is countable.

So `𝒞_0` is countable, and Theorem B gives one host `U` containing all of it. This extends `universal-simple-kazhdan-lef-groups-exist` and `simple-kazhdan-lef-host-for-countably-many-rf-groups`, which cover residually finite families via Wilson, to LEF families, including the non-RF members (v)–(vii).

## 4. Proposition D
- (1) ⇒ (2) is trivial.
- (2) ⇒ (3): subgroups of LEF groups are LEF, and a countable group has countably many finite subsets, hence countably many finitely generated subgroups.
- (3) ⇒ (1): choose one member from each isomorphism type and apply Theorem B.
- *No host for all finitely generated LEF groups.* By `continuum-many-simple-kazhdan-lef-groups` there are continuum many pairwise nonisomorphic finitely generated LEF groups, e.g. the Sturmian `G_X`. A countable group has only countably many finitely generated subgroups. □

## 5. Credit and novelty (bounded check)
- **Method:** Neumann–Neumann 1959 (wreath-product words); Ore 1951 (commutators in `Alt`); the lamplighter host of sk-universal-embedding-b on main supplies (T), simplicity and LEF.
- **Prior art:**
  - without (T), and one group at a time: Kionke–Schesler, arXiv:2304.09307. Their abstract, checked: "every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) LEF simple group";
  - residually finite families through Wilson 1980: sk-strong-1/3 on main;
  - countable locally finite groups over `Z`: `simple-kazhdan-lef-hosts-all-countable-locally-finite` on main.
- **Search:**
  - two web searches (LEF 2-generator embeddings; Neumann–Neumann 1959);
  - the jaywillmath exposition of the Neumann–Neumann method;
  - the abstracts of arXiv:2009.10571 and arXiv:2304.09307.

  I found no printed statement that every countable LEF group embeds in a finitely generated LEF group. Lemma A is folklore-level given the ultraproduct description of LEF groups (Vershik–Gordon), and I claim no priority for it.
- **Theorem B and Proposition D:** within this search there is no universal simple Kazhdan LEF host for LEF families. The bound is the search above plus a grep of main.
- **Not read:** Neumann–Neumann 1959, Hall 1959, Mal'cev.

## 6. For the note
See `research/artifacts/sk-universal-lef-host-a-proposal-2026-09-13.md`. Lemma A is about 25 source lines and self-contained. It replaces both the Ore-overgroup doubling step in the LEF iff proof and the Wilson citation behind the universal host paragraph. It also upgrades that paragraph from residually finite to LEF families, with an exact characterization.
