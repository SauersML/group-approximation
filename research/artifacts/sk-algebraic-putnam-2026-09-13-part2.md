# sk-algebraic-putnam part 2: idempotents are similar to clopen idempotents, and internal cancellation (2026-09-13)

Lane sk-algebraic-putnam. Part 1 (`sk-algebraic-putnam-2026-09-13-part1.md`) treated Laurent elements. This part classifies idempotents and proves internal cancellation. The algebraic Putnam question is then reduced to the exchange property. Everything here is ESTABLISHED and unreviewed.

## 0. Statements
Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, `R = LC(X,F) ⋊_T Z`. Write `e_W` for the indicator of a clopen set `W`.

- **Theorem DP (diagonalization).** Every idempotent `e ∈ M_n(R)` is similar, by a unit of `M_n(R)`, to a diagonal idempotent `diag(e_{W_1},…,e_{W_n})`. For `n = 1`: `e = h e_W h^{−1}` for a clopen `W` and `h ∈ R^×`.
- **Theorem IC (internal cancellation).** If `e, f ∈ R` are idempotents with `eR ≅ fR`, then `(1−e)R ≅ (1−f)R`, and `e` and `f` are similar. More precisely, `e_W ~ e_{W′}` iff `1_W − 1_{W′} = g∘T − g` for some `g ∈ C(X,Z)`, iff some `γ` in the topological full group `[[T]]` has `γW = W′`.
- **Corollary C1 (idempotent pairs are stable).** If `aR + eR = R` with `e² = e`, then `a + ec ∈ R^×` for some `c ∈ R`.
- **Corollary C2.** Every von Neumann regular element of `R` is unit-regular.
- **Corollary C3 (reduction).** If `R` is an exchange ring, then `sr(R) = 1`. This uses Camillo–Yu, Comm. Algebra 22 (1994) 4737–4749 (quoted in arXiv:1402.4706): "in an exchange ring R, every von Neumann regular element is unit regular if and only if R has stable range one".

So the algebraic Putnam theorem reduces exactly to the exchange property. Part 1 shows every Laurent element of `R` is suitable.

## 1. Setting
Orbit representation at `x`: `V = F^{(Z)}`, `fδ_t = f(T^tx)δ_t`, `uδ_t = δ_{t+1}`. It is faithful, and elements of `R` are banded matrices with entries given by locally constant functions of `T^tx`. For `n > 1` use `V^n`; nothing below changes.
- **Propagation.** `w(e)` is the least `w` such that `e` and `1 − e` map `δ_t` into `span{δ_s : |s−t| ≤ w}`.
- **Towers.** A Kakutani–Rokhlin partition `𝒫` with heights `≥ L` has cuts at the base positions. Block-diagonal operators whose blocks depend only on bounded local data lie in a tower algebra `A_𝒫 ≅ ∏_a M_{h_a}(F)` (part 1, §1). Operators supported in windows around the cuts, with local data, lie in `R` as well.

## 2. One cut
Let `e ∈ R` be idempotent with `w = w(e)`, and fix a cut `c`. Put `V_− = span{δ_t : t < c}` and `V_+ = span{δ_t : t ≥ c}`, `E = eV`, `E′ = (1−e)V`, `E_± = E ∩ V_±`, `E′_± = E′ ∩ V_±`, and `Σ = E_− + E′_− + E_+ + E′_+`.

1. **Directness.** `Σ = E_− ⊕ E′_− ⊕ E_+ ⊕ E′_+`. If `ε_−+ε_+ = −(ε′_−+ε′_+)`, both sides lie in `E ∩ E′ = 0`, and then `ε_− = −ε_+ ∈ V_− ∩ V_+ = 0`.
2. **Finite codimension, local complements.** For `t < c − w`, `δ_t = eδ_t + (1−e)δ_t` with both terms in `V_−`, so `δ_t ∈ E_− ⊕ E′_−`. Likewise for `t ≥ c + w`. So `V_± = E_± ⊕ E′_± ⊕ M_±` with `M_−` spanned by some `δ_t`, `c−w ≤ t < c`, and `M_+` by some `δ_t`, `c ≤ t < c+w`. Put `M = M_− ⊕ M_+`, so `V = Σ ⊕ M` and `dim M ≤ 2w`.
3. **Locality.** A vector `m` supported in the window `[c−w, c+w)` lies in `Σ` iff `eP_−m ∈ V_−` and `eP_+m ∈ V_+`. Then its components are `eP_±m` and `(1−e)P_±m`.
   - *Proof.* If `m = ε_− + ε′_− + ε_+ + ε′_+`, then `ε_− + ε′_− = P_−m`, and `e(P_−m) = ε_−` because `eε′_− = 0`.
   - So `M_±`, the quotient `V/Σ ≅ M`, and all decompositions are computed from the entries of `e` in the window `[c−2w, c+2w)`. These are functions of the local configuration.
4. **Two transversal images.** Let `Ĩ` and `Ĩ′` be the images of `E` and `E′` in `M ≅ V/Σ`. Then `M = Ĩ ⊕ Ĩ′`.
   - *Spanning:* `E + E′ = V`.
   - *Directness:* if `ξ ∈ E`, `η ∈ E′` and `ξ − η = σ + σ′` with `σ ∈ E_− ⊕ E_+` and `σ′ ∈ E′_− ⊕ E′_+`, then `ξ − σ = η + σ′ ∈ E ∩ E′ = 0`. So `ξ ∈ Σ`.
   - Put `p = dim Ĩ = dim E/(E_−⊕E_+)` and `p′ = dim Ĩ′`.
5. **Split transversals (Laplace).** Let `B` be the coordinate basis of `M = M_− ⊕ M_+`, of size `p + p′`. Let `pr′ : M → Ĩ` and `pr : M → Ĩ′` be the projections along `Ĩ′` and `Ĩ`. The matrix `[pr′(B) ; pr(B)]` (the columns of `B` in a basis of `Ĩ` followed by a basis of `Ĩ′`) is invertible. By the Laplace expansion along its first `p` rows, `det = Σ_T ± det pr′(B)_T · det pr(B)_{B∖T}` over `p`-subsets `T ⊆ B`. So some `T` has both `pr′(T)` a basis of `Ĩ` and `pr(B∖T)` a basis of `Ĩ′`. This works over any field. Put `S = span T` and `S′ = span(B∖T)`. Then:
   - `S ⊕ S′ = M`;
   - `S ⊕ Ĩ′ = M` and `S′ ⊕ Ĩ = M`;
   - `S = (S ∩ M_−) ⊕ (S ∩ M_+)` and likewise for `S′`, since `T` consists of coordinate vectors.
6. **The split idempotent.** Let `e_c` be the projection onto `E_− ⊕ E_+ ⊕ S` along `E′_− ⊕ E′_+ ⊕ S′`.
   - `e_c` agrees with `e` on `Σ`.
   - Its range and kernel are `(E_− ⊕ S_−) ⊕ (E_+ ⊕ S_+)` and `(E′_− ⊕ S′_−) ⊕ (E′_+ ⊕ S′_+)`, so `e_c` is block-diagonal for `V_− ⊕ V_+`.
   - `Δ_c := e_c − e` vanishes on `Σ`, hence on every `δ_t` with `|t−c| ≥ w`. On `M` its values are local. So `Δ_c` is supported in the window, with local entries.
7. **The intertwiner.** `h_c := e_ce + (1−e_c)(1−e) = 1 + Δ_c(2e − 1)` satisfies `h_ce = e_ch_c`. It is invertible:
   - `h_c` maps `E` to `range e_c` by `e_c`. On `E = E_− ⊕ E_+ ⊕ Ẽ`, with `Ẽ ≅ Ĩ`, it is the identity on `E_±`. Modulo `E_±` it is `Ĩ → S`, the projection along `S′`, which is bijective because `S′ ⊕ Ĩ = M`.
   - Likewise `h_c` maps `E′` bijectively onto `ker e_c`, because `S ⊕ Ĩ′ = M`.
   - `h_c − 1` is supported near `c`, so its inverse is `1` plus a local window operator.

## 3. Proof of Theorem DP
1. **Towers.** Choose `𝒫` with heights `L > 4w + 2`, so the windows of different cuts are disjoint. Refine the base atoms so that they determine the entries of `e` in the window of radius `4w` around every cut.
2. **All cuts at once.** At each cut, choose `M_±`, `T`, `S` and `S′` as functions of the local type, which has finitely many values. Put `e″ = e + Σ_cΔ_c`.
   - Different `Δ_c` have disjoint row and column supports, so `Δ_cΔ_{c′} = 0` for `c ≠ c′`. The one-cut identity `eΔ_c + Δ_ce + Δ_c² = Δ_c` then gives `e″² = e″`.
   - `e″` is split at every cut, since `Δ_{c′}` for `c′ ≠ c` lies on one side of `c`. So `e″` is block-diagonal, with blocks depending on local data: `e″ ∈ A_𝒫` after refining `𝒫`.
3. **Similarity.** `h = e″e + (1−e″)(1−e) = 1 + Σ_cΔ_c(2e−1)`. This is the identity plus disjoint window operators, each invertible by §2.7. So `h ∈ R^×` and `e″ = heh^{−1}`.
4. **Inside the tower algebra.** In `M_{h_a}(F)` an idempotent of rank `k_a` is similar to `diag(1,…,1,0,…,0)`. Choosing these conjugators per type gives `h′ ∈ A_𝒫^×` with `h′e″h′^{−1} = e_W`, where `W = ⋃_a ⋃_{i<k_a} T^iB_a` is clopen. ∎

For `M_n(R)`, use `V^n` and the coordinate bases of `M_± ⊆ V^n`. The result is `diag`-type: on each tower of `M_{nh_a}(F)` the idempotent is similar to a coordinate idempotent, which is a diagonal matrix of clopen indicators.

## 4. Proof of Theorem IC
1. **Equivalence gives bounded sums.** Let `x ∈ e_WRe_{W′}` and `y ∈ e_{W′}Re_W` with `xy = e_W`, `yx = e_{W′}`, and let `w` bound their propagations.
   - In the orbit representation, `x` maps `V_{W′} = span{δ_t : T^tx ∈ W′}` isomorphically onto `V_W`, with inverse `y`.
   - For an interval `J = [m, m′)`, `x` maps `V_{W′} ∩ span{δ_t : t ∈ [m+w, m′−w)}` injectively into `V_W ∩ span{δ_t : t ∈ J}`. So `#(W′-times in J) − 2w ≤ #(W-times in J)`, and symmetrically.
   - So the Birkhoff sums `Σ_{t∈J}(1_W − 1_{W′})(T^tx)` are bounded by `2w` for all `J`.
2. **Coboundary.** `x` has a dense orbit and `f = 1_W − 1_{W′}` is continuous with bounded Birkhoff sums along it. By the Gottschalk–Hedlund theorem, `f = g∘T − g` with `g` continuous. The values of `g` along the orbit differ by integers, so after a constant shift `g ∈ C(X,Z)`.
3. **Level matching.** Choose a nonempty clopen `Z` on which `g` is constant, and a Kakutani–Rokhlin partition over `Z` whose levels refine `{W, W′}`. In each tower, `Σ_{j<h} f(T^jz) = g(T^hz) − g(z) = 0`, so the tower has as many `W`-levels as `W′`-levels.
   - Let `γ` permute levels within each tower, sending `W`-levels to `W′`-levels and `(X∖W)`-levels to `(X∖W′)`-levels. Then `γ ∈ [[T]]`, `γW = W′` and `γ(X∖W) = X∖W′`.
   - For `γ = T^k` on `U_k`, the unit `w_γ = Σ_k e_{γU_k}u^k` satisfies `w_γe_Vw_γ^{−1} = e_{γV}` (as in `subshift-el-transvection-conjugacy-full-group-equivalence-proof`). So `1 − e_W` is similar to `1 − e_{W′}`.
4. **General idempotents.** By Theorem DP, `e = he_Wh^{−1}` and `f = h′e_{W′}h′^{−1}`. Then `eR ≅ fR` gives `e_W ~ e_{W′}`, so `1−e_W ~ 1−e_{W′}`, so `1−e ~ 1−f`. Similarity follows from equivalence of both the idempotents and their complements. ∎

## 5. Corollaries
- **C1.** Let `ar + es = 1` and `α = (1−e)a`, so `αr = 1−e` and `π = rα` is idempotent. `π ~ 1−e`, via `α ∈ (1−e)Rπ` and `πr(1−e) ∈ πR(1−e)`. By IC, `1−π ~ e`: take `z ∈ eR(1−π)` and `z′ ∈ (1−π)Re` with `zz′ = e` and `z′z = 1−π`. Put `g = α + z`. Then `g − a = e(z − a) ∈ eR`, and `g` is invertible with inverse `r(1−e) + z′e`:
  - `αz′ = 0`;
  - `zr(1−e) = zre(1−e) = 0`, since `(1−π)r = re`;
  - `(1−e)z = 0` and `eα = 0`.
- **C2 (Ehrlich's argument).** Let `a = axa` with `x = xax`, `e = ax` and `f = xa`. Then `e ~ f` via `a ∈ eRf` and `x ∈ fRe`. By IC there are `s ∈ (1−f)R(1−e)` and `t ∈ (1−e)R(1−f)` with `st = 1−f` and `ts = 1−e`. So `v = x + s` is a unit with inverse `a + t`, and `ava = a`.
- **C3.** Camillo–Yu with C2.

## 6. Model tests
- **A cut-crossing idempotent.** Over `F_2`, let `V` be clopen with `V ∩ TV = ∅`, and put `e = e_V + e_Vu`.
  - `e_Vue_V = e_{V∩TV}u = 0`, so `e² = e`, and `e` has propagation 1.
  - Theorem DP predicts `e ~ e_V`. Indeed `(1+e_Vu)e_V(1+e_Vu) = e_V + e_Vu = e`, with `(1+e_Vu)^{−1} = 1+e_Vu` since `(e_Vu)² = 0`.
  - The class `[1_V]` is what §4 reads off.
- **Where minimality enters.** It supplies Kakutani–Rokhlin partitions with long heights (§3.1) and a dense orbit for Gottschalk–Hedlund (§4.2). For a system with a periodic orbit, the Birkhoff sums along that orbit do not control the whole space, and step 2 is unavailable.
- **Characteristic 2.** No trace argument is used, only dimension counts and the Laplace expansion, so `F_2` is covered. Generic transversality would fail over `F_2`; the Laplace step replaces it.

## 7. Credit and search bounds
- **Imports:**
  - Gottschalk–Hedlund theorem (*Topological Dynamics*, AMS Colloq. Publ. 36, 1955): on a minimal system, a continuous function with bounded Birkhoff sums at one point is a continuous coboundary. The statement is as quoted in the secondary literature (e.g. arXiv:1101.3523, introduction). Its theorem number was not checked at source.
  - Kakutani–Rokhlin partitions (Herman–Putnam–Skau 1992).
  - Camillo–Yu 1994 (secondary quotation, arXiv:1402.4706).
  - Ehrlich's unit-regularity argument, reproduced in full above.
- **Nearest relatives:**
  - The C*-algebra facts (Putnam: tsr 1 and projections in `C(X) ⋊ Z`) use norm approximation.
  - sk-free-6 Theorem D (tower compression with index at cuts) inspired §2. There the obstruction was a Fredholm index; here it is the pair `(p, p′)`, which the Laplace choice absorbs.
- **Search:** web searches on Steinberg algebras and exchange or stable rank, V-monoids and type semigroups of ample groupoids, and Yu 1995; a grep of main for idempotent, cancellation and coboundary nodes. No algebraic idempotent classification or internal cancellation result for `LC(X,F) ⋊ Z` was found.
