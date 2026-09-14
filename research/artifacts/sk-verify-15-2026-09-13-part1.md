# sk-verify-15 part 1: non-embeddable G_X, non-exact hosts, Peirce and diagonal rigidity (2026-09-13)

Lane sk-verify-15, an independent verifier serving queue lines 35+ of `sk/queue/sk-verify-13.txt` (sk-verify-14 serves lines 18–34). This part covers lines 37–39 (sk-free-7), 42, 44, 45 (sk-free-1) and 46–48 (sk-iso-rigidity).
- Every step was re-derived by hand from the node, route and artifact on main at tip 9347f879f0.
- I did not read sk-verify-13 or sk-verify-14 artifacts on these items.
- Verdicts: PASS / PASS-WITH-FIXES / FAIL. **No FAIL.**

## Summary
| line | claim | verdict |
|---|---|---|
| 37 | `continuum-many-subshift-el-groups-pairwise-non-embeddable` | PASS (optional wiring fix W1) |
| 38 | `turing-degrees-contain-continuum-antichains` | PASS (wording W2) |
| 39 | `positive-entropy-el-groups-avoid-low-complexity-hosts` | PASS, conditional on the unreviewed `subshift-elementary-group-lef-growth-complexity-bounds` |
| 42 | `some-simple-kazhdan-lef-groups-are-not-exact` | PASS |
| 44 | `recursive-residually-finite-non-exact-groups-exist` | PASS-WITH-FIXES (F1, F2; steps checked against the arXiv source) |
| 45 | `universal-recursive-lef-host-is-not-exact` | PASS |
| 46 | `peirce-root-homomorphisms-of-e3-are-standard` | PASS |
| 47 | `peirce-root-preserving-subshift-el3-isos-force-orbit-equivalence` | PASS |
| 48 | `diagonal-recognition-makes-subshift-el3-isos-standard` | PASS-WITH-FIXES (F3 one clause; imports noted) |

## 1. sk-free-7 (lines 37–39)

**Line 38, the antichain.** Stage n handles R(e,s,t) for e < n and ordered pairs s ≠ t in 2^n.
- *Case 1:* replace σ_s by τ ⊇ σ_s with Φ_e^τ(n′)↓ for some n′ ≥ |σ_t|, and σ_t by ρ ⊇ σ_t with ρ(n′) ≠ Φ_e^τ(n′). Since n′ ≥ |σ_t|, the bit ρ(n′) is free. Extensions of pairwise incomparable strings stay pairwise incomparable.
- *Case 2:* no extension of σ_s converges at any n′ ≥ |σ_t|. So Φ_e^{x} is partial for every branch x ⊇ σ_s, and Φ_e^{x_f} ≠ x_g.
- In Case 1, the use principle gives Φ_e^{x_f}(n′) = Φ_e^τ(n′) ≠ x_g(n′).
- Every reduction x_g ≤_T x_f is some Φ_e, handled at every stage n > e once f|n ≠ g|n. So x_f and x_g are incomparable.
- f ↦ x_f is continuous and injective on 2^ω, so its image is a perfect closed set.
- PASS. **W2 (wording, 0 lines):** the model-test sentence ("the case split is what makes the construction non-effective and total") should read "the construction is not effective, since choosing between Case 1 and Case 2 is a Σ_1 question". Credit (Sacks, via Odifreddi p. 462) is pending with sk-verify-6, and this verdict does not depend on it.

**Line 37, continuum pairwise non-embeddable.**
- *Step 1.* Substituting fixed words for the generators many-one reduces WP(H) to WP(G) for f.g. H ↪ G. The degree does not depend on the generating set. ✓
- *Step 2.* α_x with binary expansion x ⊕ c, c computable and not eventually periodic, has α_x ≡_T x and is irrational. Irrationality makes the expansion unique. ✓
- *Step 3.* WP(G_{X_α}) ≡_T L(X_α) ≡_T α. This is the note's word-problem corollary, rev4 §4, refereed in rev3 by sk-rev3-referee-a. ✓
- *Step 4.* An embedding gives x ≤_T y, a contradiction. The family has cardinality continuum. ✓
- PASS. **W1 (optional wiring):** the route requires `finite-model-subshift-elementary-groups-simple-kazhdan-lef`, which carries no review line. For Sturmian X the needed facts (infinite, f.g., simple, Kazhdan, LEF) are reviewed through `topologically-free-matricial-crossed-el-simple-kazhdan-lef` (PASS, sk-verify-8 part3 and sk-verify-9). Adding it to `requires` would make the chain fully reviewed.

**Line 39, complexity obstruction (conditional).**
- *Step 1.* For ι: G_X ↪ G_Y and a local model φ of B_Y(Cr), φ∘ι is injective on B_X(r), and multiplicative on products staying in B_X(r), because ι(x), ι(y), ι(xy) ∈ B_Y(Cr). So L_X(r) ≤ L_Y(Cr). ✓
- *Step 2.* N_Y(n) ≤ (p_Y(n)+1)p_Y(n−1) ≤ 2p_Y(n)², so 9N_Y(4r+1)² ≤ 36p_Y(4r+1)⁴. ✓
- *Step 3.* At r = 500k² ≥ 125: p_X(k)·log_2 60 < 36 p_Y(2000Ck²+1)⁴. Also 36/5.9 < 7, and 2000Ck²+1 ≤ 2001Ck² since Ck² ≥ 1. ✓
- *Corollaries.*
  - Entropy: p_X(k) ≥ e^{hk}, since h = inf_k log p_X(k)/k by submultiplicativity. Then log p_Y(n) ≥ c√n along n = 2001Ck², and monotonicity of p_Y extends this to all large n with a constant loss, contradicting o(√n). ✓
  - Polynomial scales ✓.
  - Strictness: a factor map pulls back LC(Y) into LC(X) and gives G_Y ≤ G_X. ✓
- PASS, **conditional** on both bounds of `subshift-elementary-group-lef-growth-complexity-bounds`: the lower bound 60^{p_X(⌈√(r/500)⌉)} for r ≥ 125, and the upper bound 2^{9N_X(4r+1)²}. That node is unreviewed; it was queued with sk-referee-2, a finished lane. It was not re-derived here.

## 2. sk-free-1 (lines 42, 44, 45)

**Line 42, E1.**
- Osajda's Main Theorem was read at source: arXiv:1703.03791 e-print `rfneg_arXiv.tex` l.119–128, "There exist finitely generated residually finite non-exact groups defined by infinite graphical small cancellation presentations."
- RF ⇒ LEF by finite quotients injective on balls. ✓
- The host is `lef-groups-embed-in-simple-kazhdan-lef-groups` (reviewed PASS). ✓
- The inclusion is uniformly expansive (d_G ≤ C d_Γ) and effectively proper (G-balls meet Γ in finite sets), so it is a coarse equivalence onto its image. Property A passes to subspaces and is a coarse invariant (Willett quotes as recorded). ✓
- Property A is equivalent to exactness for countable groups (Guentner–Kaminker, Ozawa). ✓
- PASS. *Remark:* exactness passes to subgroups directly (Kirchberg–Wassermann), so the coarse step could be one clause; not a fix.

**Line 44, Osajda's construction is effective.** I read §3 of the arXiv source at l.300–440 on MSI (`/scratch.global/sauer354/sk/sk-verify-15/osajda`).
- The induction needs (A_i) C′(λ) labelling, (B_i) proper Z_2-walling, (C_i) φ_j nontrivial on B_j∖{1}, and (D_i) commutativity.
- **Basis:** Θ̂_1 is the Z_2-homology cover, computable. φ_1 is found by search, since G_1 is f.p. and RF (Wise–Agol, l.353–355).
- **Cover step (l.375–381):** find a finite normal cover Θ̄_{i+1} of Θ_{i+1} such that the normal closure in G_i of the words read along Θ̄_{i+1} lies in K_i = ⋂_j ker φ_i^j. Finite normal covers of a finite graph are enumerable. K_i is normal and given by finitely many maps to finite groups, so containment of the normal closure is decided on a finite generating set of the cycle words.
- **Properties (A_{i+1}) and (B_{i+1})** are proved in the text for any such cover ("Labelled paths of length ≥ λ girth … differ by a covering automorphism", l.382–392), with no further choice. Θ̂_{i+1} is the Z_2-homology cover.
- **φ_{i+1} (l.396–400):** G_{i+1} is f.p. and RF, so a terminating search over finite groups finds a map nontrivial on B_{i+1}∖{1}. Nontriviality of ball elements is decidable uniformly by McKinsey's algorithm. The maps φ_{i+1}^j for j ≤ i are compositions.
- So i ↦ Θ̂_i is recursive and the relator set is r.e. ✓
- PASS-WITH-FIXES:
  - **F1 (route, 1 clause):** "a finite generating set of cycle words" must take fundamental cycles at every base vertex of Θ̄_{i+1} (finitely many vertices, each π_1 finitely generated), since cycle words at different base points differ by conjugation by non-cycle words. With that, the decidable check is correct.
  - **F2 (route, 1 clause):** state that the recursive input sequence has girth → ∞, as the paper's non-exactness proof uses ("D–regular graphs of growing girth", l.426–428). Osajda-Monster's Remark r:recurs supplies recursive labellings for recursive graph sequences such as Cayley graphs of finite linear groups with growing girth.

**Line 45, E1′.** The recursive host `simple-kazhdan-lef-host-for-recursive-lef-groups` carries PASS review lines (sk-verify-7, -8, -11). Γ from line 44 is recursively presented, RF, hence LEF, and lies in it. The coarse and property-A steps are as in line 42. PASS.

## 3. sk-iso-rigidity (lines 46–48)

**Line 46, Theorem P.** Re-derived the route Steps 1–5.
- *Steinberg relations.* x² = 0, yx = 0 and [1+x,1+y] = 1+xy in Peirce spaces. So φ_ij is additive and bijective, and (∗) φ_ij(rs) = φ_ik(r)φ_kj(s).
- *Step 1.* φ_ij = a_ik a_ki φ_ij, so c = E_i − a_ik a_ki kills E_iME_j. Then cME_jM = 0, and fullness gives c = 0. ✓
- *Step 2.* Matrix-unit relations. ✓
- *Step 3.* φ_12(rs) = φ_12(r)a_23a_31φ_12(s) = φ_12(r)a_21φ_12(s), so θ is multiplicative. ✓
- *Step 4.* Θ is multiplicative because a_1j a_k1 = δ_jk E_1. ✓
- *Step 5.* All six index pairs checked. ✓
- PASS.

**Line 47, Corollary S.**
- *Fullness.* R_Y is simple, so M_3(R_Y) is simple and every nonzero idempotent is full. ✓
- *Hexagon.* P_ij and P_kl commute iff j ≠ k and l ≠ i. I checked the three non-commuting cases: xy spans E_iME_l ≠ 0; xy ∈ E_iME_i and yx ∈ E_jME_j span nonzero spaces. ✓
- *Relabelling.* Aut(C_6) = D_6, of order 12, realized by the free transitive S_3-relabelling of ordered pairs together with the reversal. The reversal is not a relabelling. ✓
- *Reversal.* γ(g) = (g*)^{-1} with τ the canonical anti-automorphism; γ(e_ij(r)) = e_ji(τ(r)) in characteristic 2. ✓
- Theorem P then gives M_3(R_X) ≅ M_3(R_Y). `cantor-crossed-product-matrix-ring-iso-forces-soe` (PASS) with m = 3 gives SOE. ✓
- PASS.

**Line 48, Theorem R.**
- *Step 1.* By `locally-constant-simple-group-normal-subgroups-are-open-sets`, α maps N_O onto N_{η(O)}. The lattice isomorphism of open sets gives a homeomorphism η, and supp α(f) = η(supp f).
  - β_ω(c) = α(c_U)(ω) is independent of the clopen U ∋ η^{-1}ω: compare with U∩U′, since α(c_{U∖U′}) is supported off ω.
  - β_ω is an injective homomorphism, locally constant in ω.
  - Products over clopen partitions give the pointwise formula. ✓
- *Step 2.* Out(L_3(2)) = Z/2, with inverse-transpose as the outer automorphism (recalled, as the route says). Conjugating by g ∈ LC(Ω,Q) = GL_3(B) = E_3(B) ⊆ G_Y normalizes β to γ_0^ε. ✓
- *Step 3.* If g commutes with T_12(Idem B), then g_21 = g_31 = g_23 = 0, g_11 = g_22 = c ∈ C_{R_Y}(B) = B, and c = 1 since B^× = {1}.
  - **F3 (1 clause):** "c is a unit" needs a reason. Row 2 of g is (0,c,0) and column 1 is (c,0,0)^T, so gh = I gives c h_22 = 1 and hg = I gives h_11 c = 1.
  - Then g commutes with all of A_12(R_Y), and `el3-root-subgroups-are-bicommutant-closed` (PASS) gives the double centralizer. The same holds for D_X, maximal commutative in R_X by topological freeness. ✓
- *Step 4.* γ_0(I+E_ij) = I+E_ji in characteristic 2, so α(e_ij(1_U)) = I + bpE_ij + bqE_ji with b = 1_{η(U)}. ✓
- *Step 5(iii).*
  - W(bpE_ij)W = bpE_ij and W(bqE_ji)W = bqE_ij, using pq = 0 and b,p,q ∈ B commuting. So W α(A_ij∩L) W = T_ij(B), and α(A_ij) = W A_ij(R_Y) W since W ∈ G_Y.
  - M_13 = {I + pxpE_13 + pxqE_11 + qxpE_33 + qxqE_31}, so every element has (1,2)-entry 0.
  - X_0² = Z_0² = 0 (every product term contains pq or qp).
  - [I+X_0, I+Z_0] = I + XZ + ZX + XZX + ZXZ + XZXZ. Its (1,2)-entry is psq: (XZ)_12 = p·psq; ZX and ZXZ have zero row 1; (XZX)_12 = (XZ)_11·p = 0; (XZXZ)_12 = 0.
  - Simplicity of R_Y gives psq ≠ 0, which contradicts [M_12,M_23] ⊆ M_13. ✓
- *Case (ii).* γ_X fixes L setwise and acts pointwise as γ_0. ✓
- PASS-WITH-FIXES (F3).
- *Imports:* `locally-constant-simple-group-normal-subgroups-are-open-sets` has no review line on main, and Out(L_3(2)) is recalled.
- *Wiring note:* `subshift-elementary-group-rigid-supports-are-mutual-centralizers` (PASS, sk-verify-3) is listed in `requires` but not used in the route text. This is harmless.

## 4. Not done in this part
- The Odifreddi page (with sk-verify-6).
- The bounds node behind line 39.
- The part2 classification `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit`, which is outside my queue.
