# sk-verify-18 part 4: rank-three rational spectrum invariance (2026-09-14)

Queue lines 6–7 (sk-rank3-shadows, `research/artifacts/sk-rank3-shadows-2026-09-14.md` §§2–3). Main set these as priority because they bear on the paper's rigidity Question. Neither claim carried a sk-verify-19 review line at the time of review.
- `subshift-group-isomorphism-preserves-rational-spectrum` (Theorem R), route `subshift-group-isomorphism-preserves-rational-spectrum-proof`;
- `cyclic-factor-subshift-groups-have-ring-type-shadows` (Corollary S).

## Verdict
- **Theorem R:** PASS, re-derived by hand. It is conditional only on the reviewed inputs its route requires:
  - [T] `tower-subshift-elementary-group-is-el-3k-of-base` and `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef`;
  - [C1]/[C2] `subshift-group-model-sizes-see-rational-spectrum` (PASS WITH FIXES; its fix F1 concerns only the necessity step, which Theorem R does not use);
  - [D] `el-rank-four-finite-simple-shadows-are-ring-models`;
  - [E] `rank-four-subshift-groups-see-rational-spectrum`.
- **Corollary S:** PASS, re-derived. One wording note (W2).
- No FAIL, no GAP.

## Theorem R, step by step
**Step 1 (the group with the factor has rank nm).**
- m ∈ Cyc(Y) means a continuous f: Y → Z/m with f∘T = f+1, so T(f⁻¹(i)) = f⁻¹(i+1) and Y = ⊔_{i<m} T^iU with U = f⁻¹(0) and T^mU = U.
- The route cites [T] for minimality of (U, T^m|_U). It also re-derives directly:
  - Y minimal splits into d clopen T^m-minimal components that T permutes cyclically, with d | m.
  - f is continuous and T^m-invariant, so it is constant on each component. Going once around the d components adds d to f, so d ≡ 0 mod m.
  - Hence d = m, U is one component, and T^m|_U is minimal.
  - U is infinite, and T^m|_U is expansive and zero-dimensional, so it is conjugate to a subshift.
- [T] gives R_Y ≅ M_m(R_{Y_1}) through the matrix units u^i e_U u^{−j}.
- EL_n(M_m(S)) = EL_{nm}(S): in-block transvections are commutators through another block, which exists since n ≥ 2. So G = EL_n(R_Y) = EL_{nm}(R_{Y_1}), with nm ≥ 6.

**Step 2 (nm ∈ Div(G)).**
- Only the ⊇ half of [E] at c = 1, i.e. [D] with N = nm ≥ 4, is used.
- Every sequence of finite simple groups converging to G, after rewriting the marking into the elementary marking of EL_{nm}(R_{Y_1}), is eventually PSL_{nm·d_k}(F_{q_k}). Changing the marking preserves convergence, since each finite marking is a tuple of words in the other.
- The natural dimension is well defined once it is large; Div only needs this eventually. The finitely many exceptional isomorphisms between small PSLs do not matter.

**Step 3 (transport).** Div is defined over all finite markings, so it is an isomorphism invariant. Hence nm ∈ Div(EL_n(R_X)).

**Step 4 (the group without the factor has approximants of the wrong dimension).**
- **Divisibility.** [C1] says m ∈ Cyc(X) iff m | g_r for all large r, and g_r | g_{r+1}. So m ∉ Cyc(X) gives m ∤ g_r for every r.
  - Re-derived: g_r is the gcd of cycle lengths in the strongly connected word graph of order r.
  - Cycles of order r+1 project to closed walks of the same length, so g_r | g_{r+1}.
  - A continuous f: X → Z/m depends on a finite window and increases along edges, so m | g_r for large r.
  - Conversely, a potential mod g_r gives a factor onto Z/g_r.
- **Convergence.** [C2] gives, for large N ≡ 0 mod g_r, a primitive periodic word of length N with the (r+1)-language of X.
  - With r_k → ∞ slowly and primes p_k > m large enough that N_k = g_{r_k}p_k exceeds the threshold for r_k, the models of these words map onto M_{N_k}(F_2), since the shifts are distinct.
  - Words of length ≤ λ are decided by windows of length ≤ 2λ+1 ≤ r_k+1, which are exactly the words of X. So (SL_{nN_k}(F_2), elementary marking) → (EL_n(R_X), elementary marking). This is the same window criterion as in the paper's §4.
- **Contradiction.** Transporting the marking through the isomorphism, these finite simple groups converge to G.
  - If nm | nN_k then m | g_{r_k}p_k. Since p_k > m is prime, gcd(m, p_k) = 1, so m | g_{r_k}, a contradiction.
  - So nm ∤ nN_k for every k, and nm ∉ Div(EL_n(R_X)), contradicting Step 3.

By symmetry Cyc(X) = Cyc(Y). With n = 3 this is the note's G_X.

**Model tests re-checked.**
- **Thue–Morse against Sturmian:** Thue–Morse has an odometer factor Z_2, so 2^j ∈ Cyc. A Sturmian subshift is totally minimal (its eigenvalues e^{2πikα} contain no nontrivial root of unity), so Cyc = {1}. So G_TM ≇ G_Sturmian in rank 3.
- **Two Sturmian slopes:** no conclusion, consistent with `sturmian-elementary-group-lef-growth-is-exp-r-squared`.
- **X = Y:** consistent.

**Scope as stated.** It is a necessary condition for strong orbit equivalence, relying on "rational spectrum is an SOE invariant", which is recalled and not checked here. It does not separate totally minimal subshifts. The rigidity Question stays open.

## Corollary S
- **Setup:** X infinite minimal with a cyclic factor of order m ≥ 2. By Step 1, G_X = EL_{3m}(R_{X_1}) with 3m ≥ 6.
- **Type rigidity:** for (Q_k, T_k) → (G_X, T) with Q_k finite simple, rewrite T into the elementary marking. [D] gives Q_k ≅ PSL_{3md_k}(F_{q_k}), with the marking induced by surjective ρ_k: F_1 → M_{d_k}(F_{q_k}).
- **Characteristic 2:** 2 = 0 in R_{X_1}, and [D] eventually kills every finite set of relations, so q_k is a power of 2.
- **d_k → ∞:** G_X is infinite and simple (`simple-lef-groups-are-limits-of-finite-simple-groups`).
- **Divisibility:** the ⊇ half of [E] for X_1 at N = 3m gives, for each c ∈ Cyc(X_1), 3m·c | 3md_k for large k, with k depending on c.
- **W2 (wording):** the artifact's gloss "divisible by 3·lcm of the orders in Cyc(X) visible at bounded level" should say "for each c ∈ Cyc(X_1), eventually c | d_k", which is what [E] gives. A uniform lcm bound is not claimed or needed.
- **Scope firewall:** for totally minimal X the rank-three type rigidity question stays open, as stated.

## Inputs not re-derived here
[D] and [E] themselves (sk-verify-14 part7 PASS), [T] (sk-verify-3/5 PASS), and Theorem C(2)'s existence of primitive periodic words (sk-verify-14 part2 PASS). Their named imports (Krstić–McCool through EJZ, Voronetsky's central K_2, uniqueness of natural dimension for large rank) are as recorded on those nodes.
