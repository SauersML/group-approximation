# sk-verify-15 part 3: bounded elementary generation, orbit classification of maximal subgroups, generic limits (2026-09-13)

Lane sk-verify-15. Parts 1–2: `research/artifacts/sk-verify-15-2026-09-13-part1.md`, `-part2.md`. This part covers queue lines 52–56 of `sk/queue/sk-verify-13.txt`, re-derived by hand from main at tip cdea45a115. **No FAIL.**

## Summary
| line | claim | verdict |
|---|---|---|
| 53 | `subshift-el-groups-boundedly-elementary-generated` (every h ∈ G_X is ≤ 78 elementary matrices) | PASS-WITH-FIXES (W1, W2 wording; no mathematical gap) |
| 54 | `subshift-el-groups-have-bounded-conjugation-invariant-norms` | PASS (the lower bound uses Theorem A, sk-verify-14's line 34) |
| 52 | `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit` | PASS |
| 55 | `generic-limit-of-subshift-sl-models-is-simple-kazhdan` | PASS |
| 56 | `generic-transitive-subshift-is-regular-toeplitz` (citation) | PASS, checked verbatim at source |

## 1. Line 53, Theorem D (bounded elementary generation)

**(T1) finite block Gauss reduction, S = ∏_a M_{h_a}(F_2), h_a ≥ 3.**
- *Pivot.* The left elementary matrices e_12(t′)e_13(t) make the (1,1) entry p = a_1 + t a_3 + t′a_2 a unit. Two left operations clear column 1 and two right operations clear row 1. For A′ ∈ GL_2(S): one pivot, one clear, one right. Total 9 in a fixed position pattern. ✓
- **W2 (one sentence).** "sr ≤ 2 gives t with (a_1 + t a_3, a_2) unimodular" modifies one coordinate only, which is not the literal stable range condition. It holds here componentwise.
  - In M_h(F_2) the stacked column [a_1;a_2;a_3] is injective. Put K = ker a_2, K_0 = K ∩ ker a_3, and K = K_0 ⊕ K_1.
  - a_3 is injective on K_1. Choosing t on a_3(K_1) so that (a_1 + t a_3)(K_1) meets a_1(K_0) trivially (possible since dim K ≤ h) makes a_1 + t a_3 injective on K.
  - Then sr 1 gives t′.
- *Diagonal.* diag(p,q,r) = diag(p,p^{-1},1)·diag(1,pq,(pq)^{-1})·diag(1,1,pqr), checked over a noncommutative ring. That is two Whitehead diagonals, 6 elementary matrices each.
- *Commutator.* v = pqr ∈ ∏ SL_{h_a}(F_2) is a commutator [x,y] componentwise (Thompson 1961, n ≥ 3). diag(1,1,[x,y]) is 3 Whitehead diagonals: x·y·(yx)^{-1} = [x,y] and x^{-1}y^{-1}yx = 1.
- Total 9 + 12 + 18 = 39. S is a unital subalgebra of R (the levels partition X), so these are elementary matrices over R. ✓

**(T2) index.**
- ker Q is supported within 2w of the cut, and vectors deeper than 2w lie in Im Q (take ξ = h_x^{-1}η), so Q is Fredholm.
- For a root element I+N with N² = 0, Q² = P + PNPNP = P − PN(1−P)NP in characteristic 2, which is P up to finite rank. So 2·ind Q = 0.
- Additivity under products holds up to finite rank, so ind = 0 on G. ✓

**(T3) end correction.**
- K = ker Q ⊆ L_c and V_J = Im Q + L_c. Choose M ⊆ L_c complementing Im Q, with dim M = dim K by (T2), and F = (iso K → M) ⊕ 0.
- *Injective:* Qξ ∈ Im Q and Fξ ∈ M force Qξ = 0 = Fξ, so ξ = 0.
- *Surjective:* Q is injective on L′ ⊕ V_far with image Im Q.
- (Q+F)B′ = P − Ph(1−P)h^{-1}P + FB′ = P + E and B′(Q+F) = P + E″, with E, E″ supported in [c−2W,c)². So D = −(Q+F)^{-1}E = −E″(Q+F)^{-1} is supported in the window.
- The choice of F depends only on h_x near the cut. Deciding Im Q ∩ L_c needs only preimages supported within W+w of the cut. ✓

**(T4) two ends.**
- For δ_n in the upper half of B: D_bot δ_n = 0 and P_Bh^{-1}δ_n = P_{(−∞,c_1)}h^{-1}δ_n. So Ãδ_n = (Q_top+F_top)^{-1}δ_n, supported near n or c_1, far from c_0.
- Then F_bot kills it and P_Bh = Q_top on it, so A_BÃδ_n = δ_n.
- The lower half is symmetric. V_B is finite-dimensional, so Ã = A_B^{-1}. ✓

**Assembly.**
- H_1 = ⊕_B A_B is constant across occurrences of the same refined atom, so H_1 ∈ GL_3(A_𝒫) ≅ ∏ GL_{3h_a}(F_2).
- Deep inside an occurrence, H_1^{-1}hδ_n = P_Bh^{-1}P_Bhδ_n = δ_n, since the D-terms have columns only near the ends. So Z = H_1^{-1}h − I is supported within 6W of the cuts.
- The midpoint-level partition 𝒫′ has occurrences containing exactly one cut neighbourhood at distance ≥ L/4 > 6W from their ends. So I+Z and its inverse h^{-1}H_1 lie in M_3(A_𝒫′).
- h = H_1H_2 with ≤ 39 + 39 elementary matrices in a fixed pattern. ✓
- **W1 (wording, Step 1).** The atom refinement must fix h's entries along the whole tower occurrence (height h_a, which may exceed L) plus margins of 4W, not in "the window of radius L + 4W around its tower". This is possible because the heights are bounded, and it is what H_1 ∈ M_3(A_𝒫) uses.
- The route node's constants (8w, 32w, 64w, 12w) agree with W = 2w.

**Corollary E, checked.**
- ‖h‖ ≤ 78·sup_r‖e_ij(r)‖ ≤ 156‖e_12(1)‖, by e_ij(r) = [e_ik(r), e_kj(1)] and permutation conjugation.
- cw(e_12(χ_V)) ≤ 156·(2⌊1/inf_μ μ(V)⌋ + 2) = 312(⌊1/inf_μ μ(V)⌋ + 1).
- Every element is a product of ≤ 78 involutions, since e_ij(r)² = I.
- Novelty: the lane's bounded search. I found nothing contrary.

## 2. Line 54
- Statements 1–3 follow from line 53 (PASS here), Corollary C (`subshift-el-root-elements-boundedly-normally-generated`, PASS in part 2) and Theorem B (PASS in part 2, conditional on the rank-function import).
- The lower bound 1/inf_μ μ(V) ≤ cw uses Theorem A (`subshift-el-rank-lengths-force-non-uniform-simplicity`, line 34, sk-verify-14's).
- The route `subshift-el-groups-bounded-norms-proof` requires exactly these three nodes.
- PASS.

## 3. Line 52, orbit classification of the maximal subgroups H_x
- (4)⇒(3): δ_n ↦ δ_{n−m} is R-linear. (3)⇒(2) and (2)⇔(1) are standard. ✓
- (2)⇒(3):
  - (a) over F_2, span{v,w} = {0,v,w,v+w}. Independent-triple transitivity (Theorem A, k = 3) makes G_{v,w} move every z ∉ span{v,w}, so Fix(G_{v,w}) = {v,w,v+w}. Equivariance and injectivity give φ(v+w) = φv + φw. ✓
  - (b) e_12(r)(v_1,v_2,v_3) = (v_1 + rv_2, v_2, v_3), so the common fixed set of U_12 and U_13 is V_xe_1∖0, and φ is diagonal. ✓
  - (c) equivariance under e_12(r) on (0,v,0) gives φ_1 = φ_2 and R-linearity. ✓
- (3)⇒(4): ψ_0(δ_n) is a nonzero common eigenvector of LC(X,F_2) with eigencharacter T^nx. Its support positions m satisfy T^my = T^nx, since clopen sets separate points. ✓
- PASS.

## 4. Line 55, generic limits of the finite simple models
- *§1, boundary.*
  - Entries of words of length ≤ λ have degree ≤ λ, and vanishing depends only on the (2λ+1)-language. For N > 2λ the components u^k, |k| ≤ λ, do not alias. ✓
  - A limit of orbits with unbounded periods is infinite: L_{p+1} = L_{p+1}(P) would force the orbit into P. ✓
  - Closed walks through all edges of G_{2ℓ}(Y) give periodic words with the right language and least period ≥ p_Y(2ℓ+1) → ∞. ✓
  - Finite marked groups are finitely presented, hence isolated. ✓
  - The marking with e_ij(1) transfers the reviewed homeomorphism (`subshift-algebra-groups-embed-in-marked-groups`, reviewed), since e_ij(1) = ∏_a e_ij(e_a) is a fixed word. ✓
- *Lemma 1.*
  - The edge shift of the strongly connected, non-cycle graph G_{M−1}(Y) is an infinite transitive SFT with L_M(Y_M) = L_M(Y).
  - Conversely, limits of infinite transitive subshifts are chain transitive and infinite. ✓
- *Lemma 2.*
  - (a) Perfectness: T′ is perfect (source l.154), and the clopen restriction to S[A] (source l.197) keeps approximants over A. ✓
  - (b) minimal ⇔ ∀m ∃M (clopen conditions on L_M), so the minimal subshifts form a G_δ. Density comes from Pavlov–Schmieding Theorem 1.3. The edge-shift approximants have periodic points, which gives the dense complement. ✓
  - (c) Two disjoint dense G_δ sets would contradict Baire. ✓
- *Theorem.* The simple limits are the G_X with X minimal (`subshift-elementary-group-simple-iff-infinite-minimal`, 2 review lines; `simple-kazhdan-lef-group-from-minimal-subshift`, 3 review lines). The generic properties come from Theorem 1.3. A countable set is meager in a perfect Polish space, so a generic L(X) is non-recursive and WP is unsolvable. ✓
- PASS.

## 5. Line 56, the Pavlov–Schmieding citation
I read arXiv:2203.15159v1 e-print `hausdorffArxivSubmission.tex` on MSI (`/scratch.global/sauer354/sk/sk-verify-15/ps`):
- l.234–240: Theorem `maintrans` matches the node verbatim:
  - (1) "X is a regular Toeplitz subshift (and hence is minimal, uniquely ergodic, and has zero entropy) which factors onto the universal odometer";
  - (2) "X has topological rank two";
  - (3) "X is strong orbit equivalent to the universal odometer, and in particular, the dimension group of X has rank one and hence no nontrivial infinitesimals".
- l.197: "For any nonempty shift of finite type $X$, the subshifts contained in $X$ form a clopen subset of $\Scal$ (see Lemma~\ref{SFTclopen})".
- l.154: "we prove that the space of infinite transitive subshifts is perfect".

PASS. The theorem is numbered 1.3 in the node (the compiled numbering); the source label is `maintrans`. Journal numbering is not checked, as the node says.
