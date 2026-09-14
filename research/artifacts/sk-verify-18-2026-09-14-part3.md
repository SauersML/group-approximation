# sk-verify-18 part 3: review of sk-free-9 P1 note text (2026-09-14)

Queue line 2: sk-free-9's P1, a converse to Theorem 1 ("the simple limits of the Section 2 models are exactly the G_X").
- **Artifact:** `research/artifacts/sk-free-9-proposal-2026-09-14.md`.
- **Target text:** rev4.3, main 696c4b602e, md5 0648e5f876e467e21ebf475e08b8ee92. Checked against l.240–271 (§2 models) and l.506–513 (the triviality criterion in the proof of `cor:wp`).
- **Content node:** `generic-limit-of-subshift-sl-models-is-simple-kazhdan`, already PASSed by sk-verify-15 and sk-verify-16.
- **Coordinator's candidate file:** `$SK2/rev44-candidate-free-9.md` carries the identical LaTeX block, so this verdict and F1–F3 apply to it verbatim.

## Verdict
- **Mathematics:** PASS.
- **LaTeX block as note text:** PASS-WITH-FIXES. F1 and F2 are required precision fixes (0 net lines). F3 is optional.
- **Artifact derivation:** step 3's length estimate is wrong (W1), but the error is harmless.
- P2 (marking-free expanders via Shalom) is not in this queue line and was not reviewed; its Shalom locator is still unverified, as the proposal itself says.

## Re-derivation
1. **Exact models for any periodic y.**
   - For y ∈ A^ℤ of least period N, D_y(f)δ_t = f(T^t y)δ_t is defined for every f ∈ LC(A^ℤ,F_2), since T^t y is a genuine point. It is multiplicative.
   - PD_y(f)P⁻¹δ_t = f(T^{t−1}y)δ_t = D_y(f∘T⁻¹)δ_t exactly, with P δ_t = δ_{t+1} and uf u⁻¹ = f∘T⁻¹.
   - So f u^j ↦ D_y(f)P^j is an exact ring homomorphism LC(A^ℤ,F_2)⋊ℤ → M_N(F_2). The shifts T^t y, 0 ≤ t < N, are distinct, so the images of S = {1,u^{±1}} ∪ {e_a} generate M_N(F_2), exactly as at l.265–270. The marking e_ij(φ(s)) generates EL_3(M_N(F_2)) = SL_{3N}(F_2).
2. **Triviality through windows.**
   - A word of length ≤ λ in the e_ij(s) is a matrix over LC(A^ℤ,F_2)⋊ℤ with entries Σ_{|j|≤λ} g_j u^j, each g_j depending on coordinates in [−λ,λ].
   - Its image is Σ_j D_y(g_j)P^j. For N > 2λ the P^j with |j| ≤ λ have pairwise disjoint supports, so the image is I_{3N} iff every table of the difference vanishes on the (2λ+1)-windows W_λ(y) of y.
   - This is the criterion of l.506–511, with L(X) replaced by the windows of y. That criterion holds for every subshift, since it only uses the surjection LC(A^ℤ,F_2)⋊ℤ → LC(X,F_2)⋊ℤ.
3. **Convergence ⇔ stabilization.**
   - (⇐) Immediate from step 2.
   - (⇒) The word for e_12(∏_{t<m} u^{−t}e_{v_t}u^t) (l.511–513) maps to e_12(D_y(1_{[v]})), which is trivial iff v is not a window of y. Its length depends only on m.
   - For fixed λ there are finitely many v of length 2λ+1, so convergence makes W_λ(y_k) eventually constant.
4. **The limit is G_Y.**
   - The stabilized window sets L_m = lim_k W^{(m)}(y_k) are factorial. They are extendable, because a window of a periodic sequence extends inside the same sequence, and both lengths stabilize.
   - So L = ∪_m L_m is the language of a unique subshift Y. By step 2 and the criterion for Y, the marked limit is (G_Y, (e_ij(s))).
5. **Y is infinite.**
   - If Y is finite, let p be the lcm of its periods. Every word of L of length p+1 is p-periodic.
   - For large k every (p+1)-window of y_k lies in L, so y_{k,t+p} = y_{k,t} and N_k ≤ p. This contradicts N_k → ∞.
6. **Not minimal ⇒ not simple.**
   - Take ∅ ≠ Z ⊊ Y closed and invariant, and let I = {Σ f_j u^j : f_j|_Z = 0}. It is a two-sided ideal by invariance.
   - I is nonzero: a cylinder U with U∩Y ≠ ∅ and U∩Z = ∅ gives e_U ∈ I.
   - I is proper: 1 ∉ I. Clopen sets of Z extend to Y, so R_Y/I ≅ LC(Z,F_2)⋊ℤ ≠ 0.
   - The kernel of EL_3(R_Y) → EL_3(R_Y/I) is normal, contains e_12(e_U) ≠ 1, and misses e_12(1).
7. **Exactly the G_X.**
   - A simple limit is G_Y with Y infinite (step 5) and minimal (step 6), so it is a G_X of Theorem 1.
   - Conversely, the proof of Theorem 1 realizes each G_X through these models (y_ℓ, with N_k → ∞ as G is infinite).

## Model tests re-checked
- **y_k = 0^k1^k:** Y contains 0^∞ and 1^∞, so it is not minimal, and I = {functions vanishing at 0^∞} gives a proper normal subgroup. Consistent with step 6.
- **de Bruijn cycles:** Y is the full shift, not minimal. Consistent.
- **y_ℓ from a Sturmian X (§2):** Y = X, the limit is simple. Consistent with step 7.

## Required fixes to the LaTeX (0 net lines)
- **F1:** "A proper closed invariant subset of $Y$" → "A nonempty proper closed invariant subset of $Y$". The empty set gives the whole ring, not a proper ideal.
- **F2:** "whose level subgroup is a proper normal subgroup" → "and the kernel of $\EL_3$ of the quotient map is a nontrivial proper normal subgroup of $G_Y$". The note defines no "level subgroup", and "proper" alone allows the trivial subgroup.

## Optional fix
- **F3:** "Mark $\SL_{3N}(\F_2)$ as there, with a periodic sequence $y$ of least period $N$ in place of $y_\ell$. If these marked groups converge as $N\to\infty$" → "Mark $\SL_{3N_k}(\F_2)$ as there, with periodic sequences $y_k$ of least periods $N_k\to\infty$ in place of $y_\ell$. If these marked groups converge". This makes the sequence explicit.

## Artifact nit
- **W1:** derivation step 3 says the cylinder word has "length O(m)". Nested commutators through (1) need length growing faster than linearly in m. Only finiteness for fixed m is used, so nothing breaks.
