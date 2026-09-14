# sk-cstar-genericity plan: confined torsion subgroups and the infinite-order commutator lemma (2026-09-14)

Lane sk-cstar-genericity, wave 12. The problem: is `G = G_X = EL_3(LC(X,F_2) ⋊_T Z)` C*-simple, for an infinite minimal subshift `X`?

## 0. Where the idempotent route stands (on main)
- **Theorem A** (`unit-group-confined-subgroups-idempotent-commutator-lemma`, PASS sk-verify-16 part5). Le Boudec–Matte Bon's commutator lemma holds for unit groups of rings, with orthogonal idempotents as supports. A confined `H` with an idempotent configuration (C1), (C3), (C4) contains a nonamenable rigid corner `R_ρ = EL_3(first-return crossed product)`.
- **Lemma B** (`idempotent-displacement-fails-for-polynomially-small-units`, PASS). No idempotent satisfies (C4) for `σ ∈ B_4 = {σ : 1 ∈ span_{F_2}(σ^{±1}, σ^{±2})}`, in any ring.
- **LBMB compactness** (arXiv:2006.08677, Lemma 3.3, as read by sk-cstar-idempotent). For a subset `B ⊆ G`, a confined `H` either has a confining set avoiding `B`, or some `K` in the Chabauty closure of the conjugates of `H` satisfies `K ⊆ B ∪ {1}`. That `K` is again confined, and amenable if `H` is.
- **Missing:**
  - (L3) there is no nontrivial confined `K ⊆ B_4 ∪ {1}`;
  - (L4) configurations exist for finite `P ⊆ G ∖ B_4`.

## 1. Choice: attack (L3) through "confined subgroups contain infinite-order elements"
Every element of `B_4` has finite order:
- `1 = Σ_{k∈{±1,±2}} c_k σ^k` gives, after multiplying by `σ^2`, a nonzero polynomial `P(t) = t^2 + c_1t^3 + c_{-1}t + c_2t^4 + c_{-2} ∈ F_2[t]` with `P(σ) = 0`;
- so `F_2[σ]` is a finite ring and the unit `σ` has finite order.

So (L3) follows from the stronger and cleaner statement:

**Target (IO).** Every nontrivial confined subgroup of `G_X` contains an element of infinite order.

(IO) also excludes every confined torsion subgroup, including torsion subgroups of `[[T]]` (Grigorchuk-type) and bounded-exponent subgroups. None is known to be confined, but none had been excluded in general either.

## 2. The reduction that makes (IO) a statement about single elements (proved here)

**Lemma R (pigeonhole commutators).**
- **Statement.** Let `H ≤ G` be confined by a finite `P ⊆ G ∖ {1}`, and let `(g_N)_{N∈ℕ}` be any sequence in `G`. Then there are `p ∈ P` and an infinite `S ⊆ ℕ` such that for all `N, M ∈ S`, `H` contains `g_N^{-1} [p, g_Ng_M^{-1}] g_N`, where `[a,b] = aba^{-1}b^{-1}`.
- **Proof.**
  - Confinement at `g = g_N` gives `p_N ∈ P ∩ g_NHg_N^{-1}`, i.e. `h_N = g_N^{-1}p_Ng_N ∈ H`.
  - Pigeonhole gives `p_N = p` on an infinite `S`.
  - For `N, M ∈ S` put `k = g_Ng_M^{-1}`. Then `g_M = k^{-1}g_N`, so `h_M^{-1} = g_M^{-1}p^{-1}g_M = g_N^{-1}kp^{-1}k^{-1}g_N`.
  - So `h_Nh_M^{-1} = g_N^{-1}(p·kp^{-1}k^{-1})g_N = g_N^{-1}[p,k]g_N ∈ H`. ∎

**Corollary R′.**
- **Statement.** Suppose that for every finite `P ⊆ G ∖ {1}` there is a sequence `(g_N)` such that for every `p ∈ P` and every infinite `S ⊆ ℕ`, some `N ≠ M` in `S` makes `[p, g_Ng_M^{-1}]` of infinite order. Then (IO) holds, and so does (L3).
- **Proof.** Lemma R puts a conjugate of an infinite-order element into `H`. ∎

The sequence may depend on `P`. The natural candidates are shears, since in characteristic 2, `g_N = e_31(u^N)` gives `g_Ng_M^{-1} = e_31(u^N + u^M)`, a single elementary matrix.

## 3. The single-element problem, and the tool for detecting infinite order
- **Orbit modules.**
  - For `x ∈ X`, `R` acts on `V_x = ⊕_{t∈Z} F_2δ_t` by `uδ_t = δ_{t+1}` and `fδ_t = f(T^tx)δ_t`, and `GL_3(R)` acts on `V_x^3`.
  - An entry term `f u^a` in position `(i,j)` sends `e_j ⊗ δ_t` to `f(T^{t+a}x) e_i ⊗ δ_{t+a}`.
- **Lemma E (escaping mass).**
  - **Statement.** If some finitely supported `v ∈ V_x^3` has positions of `c^m v` unbounded as `m → ∞`, then `c` has infinite order.
  - **Proof.** A finite-order `c` has a finite orbit on `v`. ∎
- **The commutator with a shear.** With `q = p^{-1}` and `s ∈ F_2[u^{±1}]`, characteristic 2 gives
  `e_31(s) q e_31(s) = q + s·(row 1 of q placed in row 3) + (column 3 of q)·s placed in column 1 + s q_13 s E_31`.
  - So `c = [p, e_31(s)] = p·e_31(s)qe_31(s)` has `c·e_3 = e_3 + col_3(p)·s·q_13`.
  - Column 3 of `c − I` is `col_3(p)·s·q_13`, and there are similar formulas for columns 1 and 2.
- **Plan for (IO) at `P`.**
  - (i) Choose one shear family per root direction, `e_ij(u^N + u^M)`.
  - (ii) Show that `p ≠ 1` makes the degree-`N` part of `c − I` nonzero for at least one direction. This is the centralizer computation: a `p` commuting with all `e_ij(F_2[u^{±1}])` is scalar, hence `1` over `F_2`.
  - (iii) Show that the degree-`N` part pushes mass by about `N` per iteration along some orbit, with no return. Minimality makes the translated coefficient supports meet along a syndetic set of `N`, and choosing `N ≪ M` in `S` keeps the two shear scales from interfering.
- **Main risk.** Step (iii) with zero divisors: products `f·(f′∘T^{-a})` of coefficient functions can vanish on orbit segments, and upper-unitriangular `p` give torsion commutators with a single shear family (`(c − I)^3 = 0` gives `c^4 = 1` in characteristic 2). Two opposite families (`e_31` and `e_13`) are needed, and the case analysis is over the Bruhat-type position of `p` on each orbit segment.

## 4. (L4), for later in this lane
- Rank-one idempotents over far-apart small tower bases reduce configurations to linear algebra over `F_2` on one tower, where the obstruction is a local identity `1 = Σ c_T T`.
- The idea is to combine (IO)-style far conjugation with the tensor trick: conjugating `P` by a far shear first makes local identities of other elements on `σ`'s tower generic.

## 5. Alternatives kept open
- **Uniform conjugate ping-pong.** For finite `P`, conjugators `g_1..g_m` such that every choice `p_i ∈ P` generates a nonamenable group. This is the full criterion; (IO) is its torsion shadow.
- **A topologically free boundary action.** No compact `G`-space with strong proximality is known. The lattice spaces have infinite valence (sk-exact-gx).

## 6. Deliverables, in order
1. This plan (landed).
2. Lemma R and Corollary R′ as a Cairn claim with route (formal, requires nothing).
3. (IO) for `P` contained in `EL_3(F_2) · e_ij(LC(X,F_2))` (constant and locally constant elements) as the first case, then general `P`.
4. If (IO) is proved: close (L3) on the open node, and queue for review.
