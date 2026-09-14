# sk-verify-15 part 2: maximal subgroups, QD targets, normal generation, two-generator attempts (2026-09-13)

Lane sk-verify-15. Part 1: `research/artifacts/sk-verify-15-2026-09-13-part1.md`. This part covers queue lines 49–51 (sk-free-2), 43 (sk-free-5), 35, 36, 41 (sk-free-6) and 40 (sk-two-generators, Attempts on an open node).
- Every step was re-derived by hand from main at tip 748e3b74d1.
- Line 34 (Theorem A of sk-free-6) belongs to sk-verify-14 and was not reviewed here.
- **No FAIL.**

## Summary
| line | claim | verdict |
|---|---|---|
| 49 | `subshift-el3-acts-two-transitively-on-orbit-modules` | PASS |
| 50 | `subshift-el3-has-continuum-many-maximal-subgroup-classes` | PASS for part1 Theorem B; the classification sentence (part2 node) not reviewed |
| 51 | `subshift-el3-parabolic-subgroups-are-maximal` | PASS |
| 43 | `kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups` | PASS |
| 35 | `transvection-normal-generation-recovers-invariant-measures` | PASS, conditional on the rank-function import (F4) |
| 36 | `subshift-el-root-elements-boundedly-normally-generated` | PASS |
| 41 | `finite-models-transvection-covering-converges-to-measure` | PASS |
| 40 | `binary-subshift-elementary-groups-are-two-generated` (Attempts A4–A5) | A4 PASS; A5-C PASS; A5-D PASS-WITH-FIX (F4′); A5-B heuristic only |

## 1. sk-free-2 (lines 49–51)

**(T1)/(T2) tools.**
- ε_ab ε_{a′b′} = δ_{ba′}ε_{ab′} from the disjoint levels.
- In the orbit module, ε_ab δ_m = [T^{m−b}x ∈ V] δ_{m−b+a}. The gaps of N = {n : T^nx ∈ V} are ≥ h, so ψ(M) acts as M on each block W_n and kills everything outside the blocks. ✓

**Line 49, Theorem A.**
- Finitely many vectors supported in [p,p+L) lie in the block W_p for a clopen V ∋ T^px with V ∩ T^jV = ∅ for 0 < |j| < L. Aperiodicity makes such V exist.
- GL_{3L}(F_2) is transitive on independent k-tuples, so ι(M) ∈ S_V ⊆ G does the job. Faithfulness follows from simplicity.
- Over F_2, distinct nonzero vectors are independent, which gives 2-transitivity.
- PASS.

**Line 50, Theorem B.**
- 2-transitive ⇒ primitive ⇒ point stabilizers are maximal. The index is ℵ_0.
- e_21(f)(δ_0e_1) = δ_0e_1 + f(x)δ_0e_2, so x ↦ H_x is injective.
- |X| = 2^{ℵ_0}, and each conjugacy class of subgroups of the countable G is countable. So there are continuum many classes, and continuum many non-isomorphic transitive G-sets. ✓
- PASS for these statements. The node's last sentence cites `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit` (part2 of the lane), which is outside my queue and not reviewed here.

**Line 51, Theorem C.**
- *Lemma C1.* I re-derived the three constructions of C ∈ S_t(B) with d(U,C) = 1, where U = W ⊕ U_1 and B = W ⊕ B_1:
  - m+t < n: C = W ⊕ U_1′ ⊕ ⟨c⟩, c ∉ U+B;
  - m+t = n, t < m: C = W′ ⊕ U_1 ⊕ ⟨b⟩;
  - t = m = n−m: C = U_1′ ⊕ ⟨a+b⟩.

  In each, U ∩ C and B ∩ C have the stated dimensions because U_1 ∩ B = 0. The case m+t > n cannot occur. Connectivity of the Grassmann graph and |H| = |Ω||Q| finish it. ✓
- *Steps 1–5 for P.*
  - p = diag(1,d_2,d_3) ∈ P ∩ G shifts S′((g^{-1})_{l1}) by T^s, and minimality aligns the supports.
  - h = e_{1l}(e_V) ∈ P ∩ S. Column 1 of k = [g′,h] is column 1 of I + g′e_VE_{1l}g′^{-1}, so k_{i1} = Σα_aβ_bε_{a,−b}.
  - The product formula needs f_a constant on T^aV and f′_b constant on V, which the choice of V gives. V ⊆ S(g′_{i1}) forces some α_a = 1, since each T^{−a}supp f_a either contains V or misses it. V ⊆ S′(·) forces some β_b = 1.
  - ι^{-1}(P) = Stab(F_2^I ⊗ e_1), so Lemma C1 gives H ∩ S = S.
  - Level ideal J: RJ ⊆ J through e_32, e_23 ∈ P. Jv ⊆ J from diag(v,v^{-1},1)e_21(r)diag(v,v^{-1},1)^{-1} = e_21(v^{-1}rv^{-1}) combined with RJ ⊆ J. Union closure and covering give 1 ∈ J. ✓
- *P′.* The row/column dual works. k_{3j} = (g′^{-1})_{3l}e_Vg′_{3j} ≠ 0 with the support sets exchanged, and J′R ⊆ J′, vJ′ ⊆ J′. ✓
- PASS.

## 2. sk-free-5 (line 43)
- *Step 1, the Kazhdan projection.* ⟨(1−π(h))ξ,ξ⟩ = (2|S|)^{-1}Σ_s‖π(s)ξ−ξ‖², checked by expanding both sides. On the invariant-free part, 1−π(h) ≥ ε²/(2|S|). So p = f(h) is a central projection onto the invariant vectors in every representation. ✓
- *Steps 2–3.* q = Ψ(1−p) is central in B. qB is a unital C*-subalgebra, and QD passes to C*-subalgebras. The ampliation ⊗ℓ²(N) is essential. Voiculescu's projections (Brown math/0111286 Prop. thm:QDcase, quoted) exist. ✓
- *Step 4.* |Tr([P_n,b]TP_n)| ≤ ‖[P_n,b]‖‖T‖Tr(P_n), so φ is a hypertrace for qB. ✓
- *Step 5.* v_g = qΨ(u_g) is a representation, and φ(v_gTv_g^*) = φ(T) makes it Bekka-amenable. qΨ(p) = 0 is its invariant-vector projection. ✓
- *Step 6.* `amenable-rep-of-kazhdan-has-fd-subrep` (derived on main: Day's trick, Powers–Størmer, (T) on HS(H)) gives a nonzero finite-dimensional subrepresentation. It is trivial by hypothesis, a contradiction. ✓
- *Consequences.* For an infinite simple Kazhdan group, a finite-dimensional unitary image is a f.g. linear group, hence RF (Mal'cev), and a quotient of a simple group, so trivial. So C*(Γ) is not QD, and its only QD quotient is C. ✓
- PASS.

## 3. sk-free-6 (lines 35, 36, 41)

**Line 35, Theorem B: ρ_max ≤ ν ≤ 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3.**
- *Lower bound.* ℓ_μ is conjugation-invariant and subadditive, so ν ≥ μ(U)/μ(V) for ergodic μ. A linear-fractional function on the simplex attains its supremum at an extreme point. ✓
- *Step 1.* Uniform ratio bounds come from weak* limits of empirical measures. χ_U and χ_V are continuous and inf_μ μ(V) > 0. ✓
- *Step 2.* The choice of δ gives s ≥ ⌈ρ_min⌉ − 1 and T ≤ ⌊ρ_max⌋ + 1, checked separately for integer and non-integer ρ. ✓
- *Steps 3–4.* The groups Γ_{j,t} and V′_t: for t ≤ s every tower has |Γ_{j,t}| = b_j, so V′_t = V. w_t is a level permutation of each tower occurrence, a unit in R through the faithful orbit representation, and w_tχ_{V′_t}w_t^{-1} = χ_{U_t}. This is consistent with uχ_Wu^{-1} = χ_{TW} in the orbit representation. ✓
- *Step 5.* D_t = diag(w,w^{-1},1)·diag(1,w²,w^{-2}) = diag(w,w,w^{-2}) ∈ G. ✓
- *Step 6.* e_12(χ_{V′_t}) = [e_13(χ_{V′_t}), e_32(χ_V)] with e_32(χ_V) = P_(13)gP_(13)^{-1}, which is 2 conjugates. ν ≤ 2T − s. ✓
- *Uniquely ergodic case and recovery of μ.* ✓
- PASS, **conditional** on (F4), faithful Sylvester rank functions rk_μ with rk_μ(χ_U) = μ(U) (`cantor-z-crossed-product-embeds-in-continuous-factor`, by citation to Ara–Claramunt, no review line on main). The Kakutani–Rokhlin partitions (F5) are standard. The lower bound also uses Theorem A (line 34, sk-verify-14's).

**Line 36, Corollary C.**
- k = [g,h] is 2 conjugates of g^{±1} and lies in the tower copy H ≅ GL_d(F_2). H is simple, so e_12(χ_{V_g}) = e_12(ε_00) ∈ H is a product of ≤ c_H H-conjugates of k^{±1}.
- Theorem B with U = X uses ρ_min ≥ 1 and gives ≤ 2⌊ρ_max⌋ + 2 conjugates for e_12(1).
- e_ij(r) = [e_ik(r), e_kj(1)] is 2 conjugates of a permutation conjugate of e_12(1)^{±1}.
- The bound M_g ≤ 2(2⌊ρ_max⌋+2)M′_g follows, and the bi-Lipschitz consequence is correct.
- PASS.

**Line 41, Theorem B_fin.**
- *Lower bound.* Rank is subadditive: N ≤ νm. ✓
- *Upper bound.* σ ∈ GL_N(F_2) = SL_N(F_2) conjugates D to a coordinate projection P_t, and diag(σ,σ,σ^{-2}) ∈ SL_{3N}(F_2). The remainder P′ ⊆ P″ ∼ D gives e_12(P′) = [e_13(P′), e_32(P″)], 2 conjugates. So ν ≤ q + 2, with equality N/m when m | N. ✓
- *Limits.* η_ℓ is shift-invariant. Cylinders of words outside L(X) get mass 0 once 2ℓ+1 ≥ |v|, so weak* limits are invariant measures on X. For uniquely ergodic X, m_ℓ/N_ℓ → μ(V) and ν·μ(V) → 1. ✓
- PASS.

## 4. sk-two-generators (line 40: Attempts A4–A5 on the open node)
- **A4, membership: PASS.**
  - In characteristic 2 with βα = 0, e_12(α)e_21(β)e_12(α) = [[1+αβ, αβα],[β, 1+βα]] = [[1+αβ,0],[β,1]], and one more e_21(β) gives diag(1+αβ,1,1).
  - 1+ε_ab = 1+αβ with α = ε_ab, β = ε_bb, and βα = ε_bbε_ab = 0 for a ≠ b.
  - P_3 is a product of transvections, so diag(v,1,1) ∈ EL_3(R). A single 1+αβ could not give v directly, since v−1 is not nilpotent.
  - The orders follow: a = c·vI has order 21 with a^15 = c and a^7 = vI; b = w·diag(1,1,v) has order 6 with b^3 = w and b^4 = diag(1,1,v).
  - diag(1,v,1) commutes with t iff (1+p)(v^{-1}+1) = 0, i.e. the levels lie in [a]. ✓
- **A5-C: PASS.** t, diag(1,v′,1), w and diag(1,1,v) are all block upper triangular for {1,2}|{3}. So the pair lies in the proper parabolic {g_31 = g_32 = 0}.
- **A5-D: PASS-WITH-FIX.** **F4′:** replace "no entry involves u of nonzero total degree on all of X" with a precise obstruction:
  - choose a nonempty clopen Y disjoint from T(V∪V′) ∪ T²(V∪V′);
  - all entries of t, c, vI and diag(1,v′,1) lie in the cut-stabilizer algebra A_Y (block diagonal for the return towers of Y), which contains LC(X,F_2) and the tower matrix units;
  - u ∉ A_Y, so e_12(u) ∉ D ⊆ GL_3(A_Y).
- **A5-B: heuristic only, not established.** Entries lie in the subring generated by u^{±1}, e_V and e_{V′}, whose diagonal part is the functions measurable for the coding of orbits by {V, V′}. When that coding separates points, the subring is all of R and there is no obstruction. "That fails for small sets V in general" is not a proof. The finite-model reducibility (A6) is evidence, as the lane says.

## 5. Not done
- Line 34 (sk-verify-14).
- The rank-function import behind line 35.
- The part2 classification node of sk-free-2.
