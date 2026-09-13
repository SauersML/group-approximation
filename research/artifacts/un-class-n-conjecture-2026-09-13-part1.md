# Class 𝔑: measured subshifts, periodic windows, and surface groups (part 1 of 2)

Lane `un-class-n-conjecture` (UN swarm), 2026-09-13. Written proofs, UNREVIEWED. Builds on
`un-rf-beyond-free` (artifacts part 1/2, review PASS in `un-review-measure-2026-09-13-part5.md`), whose
Lemma 1 (maps suffice), Lemma 2 (generators suffice), Lemma F (integer flows) and Proposition S are used
here verbatim.

## 0. Question and results

`Γ ∈ 𝔑` means: every continuous action of `Γ` on a Cantor space admitting an invariant Borel probability
measure of full support is residually finite (RF) in the sense of Kerr–Nowak. Known (reviewed): virtually
free `⊆ 𝔑`; `Z^2 ≤ Γ ⇒ Γ ∉ 𝔑`; `𝔑` is closed under subgroups and finite-index overgroups.

This part proves:
- **Theorem N.** `Γ ∈ 𝔑` iff every subshift carrying a full-support invariant probability measure is
  window-periodic (the Proposition S condition, without perfectness).
- **Corollary N1.** If `Γ ∈ 𝔑`, every SFT over `Γ` carrying an invariant probability measure has a finite orbit.
- **Corollary N2.** An amenable group with a weakly aperiodic SFT is not in `𝔑`.
- **Proposition H (handle absorption).** For the closed surface group `Γ_g` (`g >= 2`), every action pulled
  back from a measured Cantor `Z^2`-system along the handle retraction `Γ_g -> Z^2` is RF. So Labbé's non-RF
  witness does not pass to surface groups along quotients.

Part 2: invariant measures of regular Toeplitz points, a conditional minimal free non-RF action of
`SL_3(Z)`, the status of the Robinson input, and where every surface-group route stops.

## 1. Measured subshifts are the whole story

For a subshift `X ⊆ A^Γ` and finite `W ⊆ Γ` put `L_W(X) = {x|_W : x ∈ X}` and
`X_W = {c ∈ A^Γ : (g^(-1)·c)|_W ∈ L_W(X) for all g ∈ Γ}` (shift `(g·x)(h) = x(g^(-1)h)`). Call `X`
**window-periodic** if for every finite `W` there is a finite `Γ`-invariant `O ⊆ X_W` with
`{c|_W : c ∈ O} = L_W(X)`.

**Theorem N.** For a countable group `Γ` the following are equivalent:
- (a) `Γ ∈ 𝔑`;
- (b) every subshift `X ⊆ A^Γ`, `A` finite, carrying an invariant probability measure of full support, is
  window-periodic.

*Proof of (b) ⇒ (a).* Let `α : Γ ↷ Z` be a Cantor system with invariant `μ` of full support; fix finite
`F ⊆ Γ` and `ε > 0`.
- Choose a clopen partition `𝒬 = {Q_1,…,Q_k}` of mesh `< ε` and the name map
  `π : Z -> [k]^Γ`, `π(z)(γ) = i ⇔ α(γ^(-1))z ∈ Q_i`. It is continuous, and equivariant:
  `π(α(s)z)(γ) = π(z)(s^(-1)γ) = (s·π(z))(γ)`.
- `X = π(Z)` is a subshift, and `π_*μ` is an invariant measure of full support on `X`.
- Put `W = {e} ∪ F^(-1)` and take `O` from (b). For `c ∈ O` choose `ζ(c) ∈ Z` with `π(ζ(c))|_W = c|_W`
  (possible because `c|_W ∈ L_W(X)`), and let `Γ` act on `O` by the shift.
- **Closeness.** For `s ∈ F`: `π(α(s)ζ(c))(e) = π(ζ(c))(s^(-1)) = c(s^(-1)) = (s·c)(e) = π(ζ(s·c))(e)`,
  using `s^(-1) ∈ W` and `e ∈ W`. So `α(s)ζ(c)` and `ζ(s·c)` lie in one atom of `𝒬`: distance `< ε`.
- **Density.** For `z ∈ Z` the pattern `π(z)|_W` equals `c|_W` for some `c ∈ O`, so `ζ(c)` and `z` share
  the atom `Q_(π(z)(e))`.
- Lemma 1 (part 1 of `un-rf-beyond-free`) applies, because `Z` is perfect. ∎

*Proof of (a) ⇒ (b).* Let `X ⊆ A^Γ` carry `μ` of full support. Let `C = {0,1}^N` with the trivial action and
the Bernoulli measure `λ`.
- `Z = X × C` is compact, metrizable, zero-dimensional and perfect, hence a Cantor space, and `μ ⊗ λ` is
  invariant of full support. By (a), `Z` is RF.
- Fix finite `W`; metrize `X` by `d(x,x') = 2^(-max{j : x|_(B_j) = x'|_(B_j)})` for an exhaustion
  `B_1 ⊆ B_2 ⊆ …` with `e ∈ B_1`, and `Z` by the max metric. Choose `j` with `W ⊆ B_j`, `ε = 2^(-j)`,
  `F = W^(-1)`, and an RF model `(E, β)` for `(F, ε)`; write `z = (x_z, c_z)`.
- Put `y_z(λ) = x_(β(λ^(-1))z)(e)`. Then `y_(β(g)z) = g·y_z`, so `O = {y_z : z ∈ E}` is finite and invariant.
- For `w ∈ W`, closeness of `β(w^(-1))z` to `α(w^(-1))z` on `B_j ∋ e` gives
  `y_z(w) = (w^(-1)·x_z)(e) = x_z(w)`; hence `y_z|_W = x_z|_W ∈ L_W(X)`. Applied to `β(g^(-1))z` this
  gives `(g^(-1)·y_z)|_W ∈ L_W(X)`, so `O ⊆ X_W`.
- **Coverage.** For `p ∈ L_W(X)` the set `{x : x|_W = p} × C` is open and nonempty, so some `z ∈ E` is
  `ε`-close to one of its points; then `x_z|_W = p` and `y_z|_W = p`. ∎

**Corollary N1.** If `Γ ∈ 𝔑`, every SFT `Y ⊆ A^Γ` that carries an invariant probability measure contains a
configuration with finite orbit.

*Proof.* Let `μ` be invariant on `Y` and `X = supp μ`: nonempty, closed, invariant, with `μ` of full support.
Let `Y` be defined by forbidding patterns on a finite window `W_0`, and apply (b) with `W = W_0`. The finite
invariant `O ⊆ X_W` is nonempty, and every `c ∈ X_W` has all `W_0`-windows in `L_(W_0)(X) ⊆ L_(W_0)(Y)`,
so `c ∈ Y`. ∎

**Corollary N2.** Let `Γ` be amenable. If `Γ ∈ 𝔑`, every nonempty SFT over `Γ` has a finite orbit; so an
amenable group with a weakly aperiodic SFT is not in `𝔑`.

*Proof.* On an amenable group every nonempty compact invariant set carries an invariant probability measure
(weak* limits of Følner averages of a point mass). Apply N1. ∎

**Remarks.**
- Corollary N2 recovers Theorem Z for groups containing `Z^2`. Amenable groups without `Z^2` that are reported
  in the literature to admit weakly aperiodic SFTs (Baumslag–Solitar groups `BS(1,n)`, Aubrun–Kari) would be
  further non-members. That import was not obtained in this lane (arXiv API unreachable from MSI), so it is
  recorded as open, not established.
- For non-amenable groups, N1 is the binding obstruction: a non-member needs an SFT with **both** an invariant
  measure and no periodic points. Weak aperiodicity alone is not enough, since free groups have weakly
  aperiodic SFTs (Piantadosi, recalled) yet lie in `𝔑`.

## 2. Handle absorption: pullbacks to surface groups

`Γ_g = ⟨a_1,b_1,…,a_g,b_g | [a_1,b_1]⋯[a_g,b_g]⟩`, `g >= 2`, `[a,b] = aba^(-1)b^(-1)`. The **handle
retraction** `q : Γ_g -> Z^2` sends `a_1 ↦ e_1`, `b_1 ↦ e_2` and every other generator to `0`; it is a
homomorphism because `Z^2` is abelian.

**Proposition H.** Let `Z^2 ↷ Z` be a Cantor system with an invariant probability measure `μ` of full support
(for example Labbé's shift, which is not RF). Then `Γ_g ↷ Z`, `γ·z = q(γ)·z`, is RF.

*Proof.* Let `T_1, T_2` be the homeomorphisms of `e_1, e_2`. By Lemmas 1 and 2 it suffices, for each
`ε > 0`, to find a finite `Γ_g`-set `Ẽ` and `ζ : Ẽ -> Z` with `ζ(Ẽ)` `ε`-dense and `ε`-closeness on the
generators.

*Step 0 (nested partitions).* Take a clopen partition `𝒫_0` of mesh `< ε`, let `𝒫_(k+1)` be the common
refinement of `𝒫_k` and `T_i^(±1)𝒫_k` (`i = 1,2`), for `k = 0,…,3`, and `𝒫 = 𝒫_4`. For each
`P ∈ 𝒫_(k+1)` and `T ∈ {T_i^(±1)}`, `TP` lies in a single atom of `𝒫_k`.

*Step 1 (integer flows).* `F_2 = ⟨a,b⟩` acts on `Z` through `T_1, T_2`, preserving `μ`. Lemma F at the
partition `𝒫` gives finite nonempty `E_P` (`P ∈ 𝒫`) and bijections `α, β` of `E = ⊔ E_P` such that `α`
maps `E_P` into `⊔{E_(P') : P' ∩ T_1P ≠ ∅}`, `β` likewise with `T_2`, and the inverses with `T_i^(-1)`.

*Step 2 (tracking).* Let `s_1,…,s_4 ∈ {α^(±1), β^(±1)}` with matching `T_1',…,T_4' ∈ {T_i^(±1)}`, and
`z ∈ E_P`. By induction on `j`, the point `s_j⋯s_1 z` lies in some `E_(P_j)` with `P_j` contained in the
`𝒫_(4-j)`-atom `A_j ⊇ T_j'⋯T_1'P`. Indeed `P_(j+1)` meets `T_(j+1)'P_j ⊆ T_(j+1)'A_j`, which lies in one
`𝒫_(3-j)`-atom `A_(j+1)`, and `P_(j+1) ∈ 𝒫` refines `𝒫_(3-j)`, so `P_(j+1) ⊆ A_(j+1)`. For
`c = [α,β] = αβα^(-1)β^(-1)` the matching word is `T_1T_2T_1^(-1)T_2^(-1) = id`, so `c z` lies in the
`𝒫_0`-atom `Q` containing `P`. Hence `c` preserves every `E_Q = ⊔_(P ⊆ Q) E_P`, `Q ∈ 𝒫_0`.

*Step 3 (doubling).* Put `Ẽ = E × {1,2}`, `α_1 = α × id`, `β_1 = β × id`, `Ẽ_Q = E_Q × {1,2}`, and
`ζ(z,j) = ζ(z) ∈ P` for `z ∈ E_P`. Then `c̃ = [α_1, β_1] = c × id` preserves each `Ẽ_Q`.
- **Lemma D.** `c̃|_(Ẽ_Q) = τ_Q^2` for some `τ_Q ∈ Sym(Ẽ_Q)`. *Proof.* Each cycle `(x_1 … x_ℓ)` of `c` on
  `E_Q` gives the `2ℓ`-cycle `((x_1,1),(x_1,2),(x_2,1),(x_2,2),…,(x_ℓ,1),(x_ℓ,2))`, whose square is the pair of
  copies of that cycle; take the product over cycles. ∎
- **Lemma C.** For a finite set `S` and `σ ∈ Sym(S)` there is `ρ ∈ Sym(S)` with `[σ,ρ] = σ^2`. *Proof.*
  `σ^(-1)` has the cycle type of `σ`; a `ρ` reversing each cycle satisfies `ρσ^(-1)ρ^(-1) = σ`, and then
  `[σ,ρ] = σ(ρσ^(-1)ρ^(-1)) = σ^2`. ∎

*Step 4 (absorption).* Put `σ_Q = τ_Q^(-1)` and choose `ρ_Q` by Lemma C, so
`[σ_Q, ρ_Q] = σ_Q^2 = (c̃|_(Ẽ_Q))^(-1)`. Let `α_2 = ⊔_Q σ_Q`, `β_2 = ⊔_Q ρ_Q`, and `α_i = β_i = id` for
`i >= 3`. Then `[α_1,β_1][α_2,β_2]⋯[α_g,β_g] = c̃ · c̃^(-1) = id`, so `Ẽ` is a `Γ_g`-set.

*Step 5 (closeness).* For `z̃ ∈ Ẽ_P`, the points `ζ(α_1 z̃)` and `T_1ζ(z̃)` lie in the `𝒫_3`-atom containing
`T_1P`, hence are `ε`-close; likewise for `β_1` and the inverses. `α_2, β_2` preserve each `Ẽ_Q`, so they move
`ζ` inside one `𝒫_0`-atom, matching `q(a_2) = q(b_2) = 0`; the handles `i >= 3` act trivially on both sides.
`ζ(Ẽ)` meets every atom of `𝒫`, so it is `ε`-dense. Lemma 1 finishes. ∎

**What Proposition H says and does not say.**
- Non-RF-ness passes to subgroups and to factors, but **not** along quotient maps of the acting group:
  Labbé's shift is non-RF for `Z^2`, while its pull-back to `Γ_g` is RF.
- The proof needs a spare handle acting trivially at the coarse scale to absorb the relator defect. A general
  action of `Γ_g` has no spare handle. Part 2 §6 records where that route stops.
- No novelty search was run. The integer-flow step is Kerr–Nowak's (Lemma F); the squaring trick is elementary.
