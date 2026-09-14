# sk-free-2: the generic limit of the note's finite simple models is simple (2026-09-13)

Lane sk-free-2. Status: ESTABLISHED by the argument below, UNREVIEWED. It goes beyond the boundary theorem of `research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md` §3–4, which is re-derived in §1 in the form needed here.

## 0. Setting
- `A` is a finite alphabet. `F` is the free `F_2`-algebra on `τ_+, τ_−` and `τ_a` (`a ∈ A`), and `Λ = EL_3(F)` is marked by `Σ = {e_ij(1), e_ij(τ_s)}`.
- **Models.** For a periodic word `y` over `A` of least period `N`, `ρ_y : F → M_N(F_2)` sends `τ_± ↦ P^{±1}` (the cyclic shift) and `τ_a ↦ D_y(e_a)` (the diagonal `[y_n = a]`). It maps `Λ` onto `SL_{3N}(F_2)`, and the marked group is `M_y = (SL_{3N}(F_2), ρ_y(Σ))`.
- **Limits.** For a subshift `Y ⊆ A^Z`, `π_Y : F → R_Y = LC(Y,F_2) ⋊ Z` sends `τ_± ↦ u^{±1}` and `τ_a ↦ e_{[x_0 = a]}`. Put `G_Y = (EL_3(R_Y), π_Y(Σ))`.
- **Admissible subshift:** infinite, with every word graph `G_m(Y)` (vertices `L_m(Y)`, edges `L_{m+1}(Y)`) strongly connected; equivalently, infinite and chain transitive.

## 1. The closure of the models (boundary theorem, re-derived)
- **Relations of length `≤ λ`.** A word of length `≤ λ` in `Σ` has matrix entries in `F` of degree `≤ λ` (note, §1).
  - Such an entry vanishes in `R_Y` iff the cylinder coefficients (radius `≤ λ`) of each `u^k`-component vanish on `Y`. This depends only on `L_{2λ+1}(Y)`.
  - For `N > 2λ` the components `u^k`, `|k| ≤ λ`, do not alias modulo `N`. So the entry vanishes under `ρ_y` iff the same coefficients vanish on the orbit `O_y`, which depends only on `L_{2λ+1}(O_y)`.
- **Consequences.**
  - If `L_{2λ+1}(O_y) = L_{2λ+1}(Y)` and `N > 2λ`, then `M_y` and `G_Y` have the same relations of length `≤ λ`.
  - A sequence `M_{y_k}` with `N_k → ∞` converges iff the languages of `O_{y_k}` converge (for each `m`, `L_m` is eventually constant). The limit is `G_Y` for the limit subshift `Y`, and `Y` is admissible: word graphs of periodic orbits are strongly connected, and a limit of orbits of unbounded period is infinite.
  - Conversely, for admissible `Y` and each `ℓ`, an Euler-type closed walk covering all edges of `G_{2ℓ}(Y)` gives `y_ℓ` with `L_{2ℓ+1}(O_{y_ℓ}) = L_{2ℓ+1}(Y)` and `N_ℓ ≥ p_Y(2ℓ+1) → ∞`. So `M_{y_ℓ} → G_Y`.
  - Models with bounded `N` are finitely many finite marked groups, hence isolated.
- **Topology.** `Y ↦ G_Y` is a homeomorphism of the compact space of subshifts onto a closed set of marked groups (`subshift-algebra-groups-embed-in-marked-groups`, item 3). That node uses the marking without `e_ij(1)`; `e_ij(1) = ∏_a e_ij(e_{[x_0=a]})` is a fixed word, so the homeomorphism transfers.
- **Conclusion.** The closure of `{M_y}` is the disjoint union of the isolated `M_y` and `𝒞_A = {G_Y : Y admissible over A}`, which is homeomorphic to the space `Adm_A` of admissible subshifts.

## 2. Admissible = the closure of the infinite transitive subshifts
**Lemma 1.** `Adm_A = T̄′[A] := T̄′ ∩ S[A]`, in the notation of `generic-transitive-subshift-is-regular-toeplitz`.

*Proof.*
- **(⊆)** Let `Y` be admissible and `M` large.
  - `G_{M−1}(Y)` is strongly connected, and it is not a single cycle: otherwise every point of `Y` would follow the cycle, and `Y` would be a finite orbit.
  - The edge shift of this graph, `Y_M` (all bi-infinite walks), is an irreducible SFT with at least two distinct cycles. So it is infinite and transitive, and `L_M(Y_M) = L_M(Y)`.
  - Hence `Y` is a limit of infinite transitive subshifts.
- **(⊇)** Let `Y_k → Y` with `Y_k` infinite transitive.
  - Word graphs of transitive subshifts are strongly connected, and `G_m(Y) = G_m(Y_k)` for large `k`. So `Y` is chain transitive.
  - If `Y` were finite, it would be one periodic orbit `P` of period `p`. `L_{p+1}(Y_k) = L_{p+1}(P)` would force `Y_k ⊆ P`, contradicting infiniteness. ∎

**Lemma 2.**
- (a) `Adm_A` is a Cantor set (for `|A| ≥ 2`).
- (b) The minimal subshifts form a dense `G_δ` in `Adm_A`, whose complement is also dense.
- (c) The set of minimal subshifts is not `F_σ`.

*Proof.*
- **(a)** `S[A]` is compact metrizable and zero-dimensional (the basic sets `{Y : L_m(Y) = L}` are clopen). `Adm_A` is closed. Pavlov–Schmieding prove `T′` perfect (arXiv:2203.15159, p. 2: "we prove that the space of infinite transitive subshifts is perfect"), so its closure is perfect. It is nonempty for `|A| ≥ 2`.
- **(b) `G_δ`.** `Y` is minimal iff `∀m ∃M`: every word of `L_M(Y)` contains every word of `L_m(Y)`. For fixed `(m,M)` this condition depends only on `L_M(Y)`, so it is clopen.
- **(b) Density** follows from `generic-transitive-subshift-is-regular-toeplitz` restricted to the open set `T̄′[A]`.
- **(b) Dense complement.** The approximants `Y_M` of Lemma 1 contain periodic points and are infinite, so they are not minimal.
- **(c)** If the minimal set were `F_σ`, its complement would be a dense `G_δ` disjoint from a dense `G_δ`, contradicting Baire. ∎

## 3. Theorem (generic limits)
Let `|A| ≥ 2`. In the Cantor set `𝒞_A` of infinite marked limits of the finite simple models `(SL_{3N}(F_2), ρ_y(Σ))`:
1. **Simple limits.** The simple groups form a dense `G_δ` that is not `F_σ`. They are exactly the `G_X` with `X` infinite minimal (`subshift-elementary-group-simple-iff-infinite-minimal`), and each is an infinite simple Kazhdan LEF group (`simple-kazhdan-lef-group-from-minimal-subshift`). The non-simple limits are dense.
2. **Generic limit.** A generic limit is `G_X` with `X` a regular Toeplitz subshift, uniquely ergodic, of zero entropy, and strongly orbit equivalent to the universal odometer. So the dimension group `K_0(R_X) ≅ C(X,Z)/(1−T)` has rank one (`subshift-crossed-product-k0-is-coinvariant-group`; Pavlov–Schmieding Theorem 1.3(3)).
3. **Word problem.** A generic limit has unsolvable word problem, of Turing degree that of `L(X)` (`subshift-elementary-group-word-problem-degree`). Only countably many languages are recursive, and a countable subset of a perfect Polish space is meager.

*Proof.* §1 identifies `𝒞_A ≅ Adm_A` homeomorphically. Lemma 2 transports (1), Pavlov–Schmieding Theorem 1.3 gives (2), and counting gives (3). ∎

## 4. Remarks and scope
- **Contrast.** In the space `S′` of all non-isolated subshifts, a generic subshift has every point bi-asymptotic to finitely many periodic orbits (Pavlov–Schmieding Theorem 1.2). There the generic `G_Y` is not simple. Genericity of simplicity is special to the closure of the finite models, i.e. to chain transitivity.
- **Not claimed.**
  - `Π^0_2`-completeness of simplicity (it would follow from Wadge's lemma, recalled, not checked);
  - statements over `F_q` or `n ≠ 3` (the same argument should apply);
  - anything about the lamplighter hosts.
- **Credit.**
  - The boundary theorem is the pestov91 four-regular artifact §3–4.
  - The genericity input is Pavlov–Schmieding, arXiv:2203.15159 (Nonlinearity 36 (2023)); journal numbering not checked.
  - Novelty search: main grep only ("generic", "Baire", "Pavlov", "chain transitive").
