# sk-verify-14, part 5: review of sk-free-5 (Brown's Question 3: weakly dense C*(F_∞), and vanishing Popa corners) (2026-09-13)

Lane sk-verify-14, queue `sk/queue/sk-verify-13.txt`, lines 32–33.
- **Target:** `research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md`, the two claim nodes and their routes.
- **Method:** every step re-derived by hand. No other review was on main when I started.

## 0. Verdicts

| claim | verdict |
|---|---|
| `separable-ii1-factors-have-weakly-dense-full-free-group-cstar` (T1) | **PASS** (novelty caution, §2.3) |
| `kazhdan-group-factor-popa-corners-have-vanishing-trace` (Lemma S) | **PASS** |

## 1. Statement fidelity
- **Source check.** Brown, arXiv:math/0111286, e-print on MSI (`/scratch.global/sauer354/sk/sk-strong-7/br/src`), l.3134: "contain a weakly dense, QD C$^*$-subalgebra? How about a Popa algebra?" This matches the lane's quotation.
- **No trace condition.** I agree with the lane's reading. An amenable trace on a weakly dense subalgebra would force injectivity of the factor, yet Brown–Dykema answer the free group case positively. So the printed QD clause asks only for a weakly dense quasidiagonal C*-subalgebra, and T1 answers it for every separable II_1 factor.
- **The Popa clause** needs simplicity. T1 does not give it, and the node says so.

## 2. T1
### 2.1 Steps re-derived
1. **Norming family.**
   - C*(F_2) is RFD (Choi 1980). C*(F_∞) ⊆ C*(F_2), because full group C*-algebras of subgroups embed. So C*(F_∞) is RFD.
   - sup_k‖σ_k(x)‖ is a C*-seminorm that equals ‖x‖ on a dense set. Both sides are 1-Lipschitz, so they agree everywhere.
   - Repeating each σ_k infinitely often gives (N): sup_{j≥m}‖ρ_j(x)‖ = ‖x‖ for every m.
2. **Corners.**
   - τ(q_j) = 2^{−j−1}, so τ(1−e_i) = Σ_{j≥i}2^{−j−1} = 2^{−i}.
   - Each corner q_jMq_j is a II_1 factor, so it contains a unital copy of M_{d_j}.
3. **Lemma U.**
   - With x = eye: x*x = ey*ye − ey*(1−e)ye = e − ey*(1−e)ye, so ‖e − x*x‖_2 ≤ ‖(1−e)ye‖_2 ≤ δ^{1/2}.
   - Polar decomposition in the finite algebra eMe extends v to a unitary w with x = w|x|, since e − v*v ~ e − vv*.
   - ‖w − x‖_2 = ‖e − |x|‖_2 ≤ ‖e − |x|²‖_2, from (1−t)² ≤ (1−t²)² on [0,1].
4. **Generators.**
   - e_i and the q_j (j ≥ i) are orthogonal and sum to 1, so z_i = w_i + Σ_{j≥i}r_j(a_i) is unitary. The sum converges strongly.
   - π is given by the universal property.
5. **Injective.**
   - For i ≤ m ≤ j, q_j ≤ 1 − e_i, so q_j reduces z_i^{±1} with compression r_j(a_i^{±1}).
   - For a polynomial x in a_1^{±1}, …, a_m^{±1}, π(x)q_j = θ_j(ρ_j(x)), so ‖π(x)‖ ≥ ‖ρ_j(x)‖ for all j ≥ m. By (N), π is isometric on C[F_∞], hence injective.
6. **Weakly dense.**
   - z_i − y_k = (w_i − e_iy_ke_i) − e_iy_k(1−e_i) − (1−e_i)y_ke_i + (Σ_{j≥i}r_j(a_i) − (1−e_i)y_k(1−e_i)).
   - The four terms are bounded by δ_i^{1/2}, δ_i^{1/2}, δ_i^{1/2} and 2δ_i^{1/2}, the last by ‖(1−e_i)T(1−e_i)‖_2 ≤ ‖T‖‖1−e_i‖_2. So ‖z_i − y_k‖_2 ≤ 5·2^{−i/2}.
   - ‖(z−y)x̂‖ = ‖(z−y)x‖_2 ≤ ‖z−y‖_2‖x‖, and the net is bounded, so z_i → y_k strongly along κ^{−1}(k).
7. **Properties.** A separable RFD C*-algebra is QD. C*(F_∞) has the LLP (Kirchberg).

### 2.2 Model test
The construction never uses (T), fullness or Connes-embeddability. For M = R it is consistent with the AF subalgebras. The trace τ∘π is produced by the construction, not fixed in advance.

### 2.3 Novelty caution
- T1 is elementary: norming representations on vanishing corners plus 2-norm approximation of generators.
- A remark of this kind may exist in the RFD literature (Hadwin, Shulman; not checked) or around Brown's Corollary items (4)–(6).
- The node says "not found in the bounded search", which is the right wording. The note should not present T1 as new without a wider search.

## 3. Lemma S
1. **Spectral gap.**
   - The conjugation representation on ℓ²(G∖{e}) has no invariant vectors, because G is ICC.
   - The Kazhdan pair gives max_s‖λ_sξλ_s* − ξ‖_2 ≥ ε_S‖ξ‖_2.
   - For ξ = x − τ(x), ‖λ_sξλ_s* − ξ‖_2 = ‖[λ_s,x]‖_2, which is (SG).
2. **Half-trace projection.**
   - e = Σ_rΣ_a f^{(r)}_{a1}g_rf^{(r)}_{1a}, with g_r ≤ f^{(r)}_{11} of half trace, is a projection.
   - e commutes with the matrix units, e ≤ p, and τ(e) = τ(p)/2.
3. **Almost commutation.**
   - [e,(1−p)y(1−p)] = 0.
   - ‖[e,py(1−p)]‖ ≤ ‖py(1−p)‖ = ‖[p,y](1−p)‖ ≤ η, and likewise for (1−p)yp.
   - [e,pyp] = [e,pyp−b] has norm ≤ 2η.
   - Total ‖[e,y_s]‖ ≤ 4η.
4. **Conclusion.**
   - ‖[e,λ_s]‖_2 ≤ 4η + 2δ.
   - (SG) gives ‖e − τ(e)‖_2 ≤ ε_S^{−1}(4η+2δ).
   - ‖e − τ(e)‖_2² = τ(e)(1−τ(e)) ≥ τ(e)/2 = τ(p)/4.
- **Model test (R5 of the artifact).** Consistent: corners of T1's algebra have trace ≤ 2^{−i−1}, within the bound 400ε_S^{−2}2^{−i}.
- **Not checked.** The extension to full factors through Connes's spectral-gap sets (recalled by the lane).
