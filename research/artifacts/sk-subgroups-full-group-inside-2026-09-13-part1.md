# The topological full group inside G_X, part 1

Lane `sk-subgroups` (SK swarm), 2026-09-13. Written proofs, UNREVIEWED (queued with sk-referee-2).
Part 2 has: the firewall on the Whitehead diagonal map, other subgroups, prior art, and model tests.

## 0. Summary
- **Corollary A.** For every infinite minimal subshift `X`, `g ↦ diag(w_g, 1, 1)` embeds the commutator subgroup `[[T]]'` of the topological full group in `G_X = EL_3(LC(X,F_2) ⋊_T Z)`.
  - `[[T]]'` is infinite, finitely generated and simple (Matui), and amenable (Juschenko–Monod).
  - So an infinite f.g. simple amenable group sits inside the infinite simple Kazhdan group `G_X`, and both come from the same subshift.
  - The proof is two displayed identities.
- **Theorem B.** The whole topological full group embeds: `g ↦ diag(w_g, u^{-I(g)}, 1)`, where `I` is the index map. The proof is self-contained and specific to `F_2`.
- Under the note's finite models, `w_g` goes to a permutation matrix of `Z/NZ`, which is the periodic approximation of `g` (§3).

## 1. Setting and full-group units
- `(X,T)` is an infinite minimal Cantor system. An infinite minimal subshift is perfect, so it is a Cantor set.
- Conventions of `simple_kazhdan_sofic_group.tex`:
  - `(Tx)_n = x_{n+1}`;
  - `R = LC(X,F_2) ⋊_T Z = {Σ_j f_j u^j}`, with `u f u^{-1} = f∘T^{-1}`, so `u e_V u^{-1} = e_{TV}`;
  - `G = EL_3(R)` and `e_ij(r) = I_3 + r E_ij`.
- `T` has no periodic points, so the representation `Σ_j f_j u^j` is unique.
- `[[T]]` is the group of homeomorphisms `g` of `X` with a continuous `n_g : X → Z` such that `g(x) = T^{n_g(x)} x`.
  - `n_g` is unique because there are no periodic points.
  - `n_g` is locally constant and takes finitely many values.
  - Write `A_n(g) = {n_g = n}`.

**Lemma 1.** Put `w_g = Σ_n u^n e_{A_n(g)}`. Then:
- (i) `w_g w_h = w_{gh}`, so `w_g` is a unit with inverse `w_{g^{-1}}`;
- (ii) `w_g e_V = e_{gV} w_g` for every clopen `V`;
- (iii) `g ↦ w_g` is injective.

*Proof.*
- (i) `u^n e_A u^m e_B = u^{n+m} e_{T^{-m}A ∩ B}`. So the coefficient set of `u^k` in `w_g w_h` is the union of `{n_h = m} ∩ T^{-m}{n_g = n}` over `n + m = k`. On `{n_h = m} ∩ T^{-m}{n_g = n}`, `gh = T^{n+m}`, so this union is `{n_{gh} = k}`.
- (ii) `w_g e_V = Σ_n u^n e_{A_n∩V} = Σ_n e_{T^n(A_n∩V)} u^n`.
  - `T^n(A_n∩V) = g(A_n∩V)`, and these sets partition `gV`.
  - `Σ_n e_{T^nA_n} u^n = w_g`.
  - So `w_g e_V = e_{gV} w_g`.
- (iii) Writing `w_g = Σ_n e_{T^nA_n} u^n`, the coefficient of `u^0` is `e_{A_0}`. If `w_g = 1`, then `A_0 = X` and `g = 1`. ∎

**Lemma 2 (Whitehead).** For units `a, b` of `R`:
- `diag(a, a^{-1}, 1) = e_12(a) e_21(a^{-1}) e_12(a) · e_12(1) e_21(1) e_12(1) ∈ G`;
- `diag(aba^{-1}b^{-1}, 1, 1) = diag(a,a^{-1},1) · diag(b,b^{-1},1) · diag((ba)^{-1}, ba, 1) ∈ G`.

*Proof.* In characteristic 2:
- `e_12(a) e_21(a^{-1}) = [[0,a],[a^{-1},1]]`;
- times `e_12(a)` this gives `w(a) = [[0,a],[a^{-1},0]]`;
- `w(a) w(1) = diag(a, a^{-1})`.
The second identity is a product of diagonal matrices: the first slot is `ab(ba)^{-1} = aba^{-1}b^{-1}`, the second is `a^{-1}b^{-1}ba = 1`.
Over any ring the same identities hold with signs: `e_12(a)e_21(-a^{-1})e_12(a) = [[0,a],[-a^{-1},0]]` and `w(a)w(-1) = diag(a,a^{-1})`. ∎

**Corollary A.** `g ↦ diag(w_g, 1, 1)` is an injective homomorphism `[[T]]' → G`.
- It is a homomorphism by Lemma 1(i) and injective by Lemma 1(iii).
- Every `g ∈ [[T]]'` is a product of commutators, so `w_g` is a product of commutators of units, and Lemma 2 puts `diag(w_g,1,1)` in `G`.
- The same argument works over any coefficient field `k`, in `EL_3(LC(X,k) ⋊ Z)`, with the signed identities.

Properties of `[[T]]'`, verified from the sources:
- Matui, *Some remarks on topological full groups of Cantor minimal systems*, arXiv:math/0404117v3 (Internat. J. Math. 17 (2006); Crossref check in part 2):
  - note after Theorem 4.8: "It follows that the commutator subgroup D([[φ]]_0) coincides with D([[φ]]).";
  - Theorem 4.9: "Let (X, φ) be a Cantor minimal system. The commutator subgroup D([[φ]]_0) is simple.";
  - Theorem 5.4: "Let (X, φ) be a Cantor minimal system. The commutator subgroup D([[φ]]_0) is finitely generated if and only if (X, φ) is conjugate to a minimal subshift.";
  - Definition 2.7 defines the index map `I(γ) = ∫ n_γ dμ` and says `I` "is a surjective homomorphism from [[φ]] to Z";
  - p. 4: "every element of [[φ]]_x is of finite order".
- Juschenko–Monod, *Cantor systems, piecewise translations and simple amenable groups*, arXiv:1204.2132v3 (Ann. of Math. 178 (2013)), Theorem A: "The topological full group of any minimal Cantor system is amenable."
- `[[T]]'` is infinite: the order-3 elements `γ_U` of Matui §5 are distinct for distinct small cylinders `U`.

## 2. The whole topological full group (F_2)
**Index by flux.** Fix `y ∈ X` and identify its orbit with `Z` through `n ↦ T^n y`.
- `g ∈ [[T]]` acts on `Z` by `ĝ(n) = n + n_g(T^n y)`, with displacement at most `‖n_g‖_∞`.
- Let `N = {0,1,2,…}` and `ind(A,B) = |A∖B| − |B∖A|` for sets with finite symmetric difference.
- `ind` is additive, `ind(A,C) = ind(A,B) + ind(B,C)`, and invariant under bijections.
- Define `I(g) = ind(ĝ^{-1}N, N)`. Then `I(gh) = ind(ĥ^{-1}ĝ^{-1}N, ĥ^{-1}N) + ind(ĥ^{-1}N, N) = I(g) + I(h)`, so `I` is a homomorphism.
- `I(T) = 1`, and `I(g) = 0` whenever `g` has finite order.
- This agrees with Matui's `∫ n_g dμ`, but the proof below does not use that.

**Lemma 3 (tower permutations).**
- *Setting:* `W` clopen, `h_0 ≥ 1`, the levels `T^aW` (`0 ≤ a < h_0`) pairwise disjoint, `π` a permutation of `{0,…,h_0−1}`, and `g ∈ [[T]]` equal to `T^{π(a)−a}` on `T^aW` and to the identity off the tower.
- *Conclusion:* `diag(w_g, 1, 1) ∈ G`.

*Proof.*
- `E_ab = e_{T^aW} u^{a−b}` satisfy `E_ab E_cd = δ_bc E_ad`. Let `e = Σ_a E_aa`. Then `w_g = (1−e) + Σ_a E_{π(a),a}`.
- The map `Φ(A) = (1−e) I_3 + Σ A_{(p,a),(q,b)} E_ab E_pq` is a homomorphism `GL_{3h_0}(F_2) → GL_3(R)`.
- Φ sends the elementary transvections to elements of `G`:
  - for `p ≠ q`, `I_3 + E_ab E_pq = e_pq(E_ab)`;
  - for `p = q` and `a ≠ b`, `I_3 + E_ab E_pp = [e_pq(E_ab), e_qp(E_bb)]` for any `q ≠ p` (disk l.205–215).
- These transvections generate `GL_{3h_0}(F_2) = SL_{3h_0}(F_2)`, so `Φ(GL_{3h_0}(F_2)) ⊆ G`.
- `diag(w_g,1,1) = Φ(diag(P_π, I, I))`. ∎

**Lemma 4.** `[[T]]` is generated by `T` and products of Lemma-3 elements over disjoint towers.

*Proof.* Let `g ∈ [[T]]`, `k = I(g)`, `g_1 = T^{-k} g` (so `I(g_1) = 0`), and `M = max(1, ‖n_{g_1}‖_∞)`.
1. *Correcting the flux near 0.*
   - Let `A = {n < 0 : ĝ_1(n) ≥ 0}` and `B = {n ≥ 0 : ĝ_1(n) < 0}`. Then `|A| = |B|`, `ĝ_1(A) ⊆ [0, M)` and `ĝ_1(B) ⊆ [−M, 0)`.
   - Let `σ` be an involution of `Z` exchanging `ĝ_1(A)` with `ĝ_1(B)` and fixing everything else. It is supported in `[−M, M)`.
   - Choose a clopen `V ∋ y` with the sets `T^jV`, `|j| ≤ 2M`, pairwise disjoint.
   - Let `σ̃ = T^{σ(j)−j}` on `T^jV` for `−M ≤ j < M`, and the identity elsewhere. This is a Lemma-3 element: the tower over `T^{−M}V` has height `2M`.
   - If `T^m y` lies in this tower, then `m = j + n'` with `T^{n'}y ∈ V`. Either `n' = 0`, or `|n'| > 4M`, in which case `|m| > 3M` and `σ̃` moves `T^m y` by less than `2M`.
   - So on the orbit of `y`, `σ̃` acts as `σ` on `[−M, M)`, fixes `[−3M, 3M] ∖ [−M, M)`, and moves no point across 0.
   - Put `h = σ̃ g_1`. Nonnegative images `ĝ_1(n)` with `n ≥ 0` avoid `ĝ_1(A) ∪ ĝ_1(B)`, so `σ` fixes them. So `h` maps `O^+(y) = {T^n y : n ≥ 0}` onto itself, and also `O^−(y)` onto itself.
2. *`h` permutes the levels of a Kakutani–Rokhlin partition.*
   - If `h = 1` we are done. Otherwise put `M' = ‖n_h‖_∞ ≥ 1`.
   - Choose a clopen `Y ∋ y` such that `n_h` is constant on `T^jY` for `|j| ≤ M'` and every return time to `Y` exceeds `2M'`.
   - Split `Y` by first return time `r` into pieces `Y_r`, with towers `T^jY_r`, `0 ≤ j < r`. Refine the bases so that `n_h` is constant on every level.
   - For `x = T^j z` with `z` in a base of height `r`:
     - if `M' ≤ j < r − M'`, then `h(x)` is in the same tower;
     - if `0 ≤ j < M'`, then `x ∈ T^jY`, so `n_h(x) = n_h(T^j y) =: c_j`. Since `h(T^jy) ∈ O^+(y)`, `0 ≤ j + c_j ≤ 2M' < r`;
     - if `r − M' ≤ j < r`, then `x ∈ T^{−i}Y` with `i = r − j ∈ [1, M']`, so `n_h(x) = c_{−i}`. Since `h(T^{-i}y) ∈ O^−(y)`, `r − 2M' ≤ j + c_{−i} < r`.
   - So `h` maps each tower onto itself. As `n_h` is constant on levels, `h` permutes the levels, and it is a product of Lemma-3 elements over the finitely many towers.
3. So `g = T^k σ̃^{-1} h`. ∎

**Theorem B.** `φ(g) = diag(w_g, u^{−I(g)}, 1)` is an injective homomorphism `[[T]] → G`.

*Proof.*
- `φ` is a homomorphism slot by slot (Lemma 1(i) and additivity of `I`), and injective by Lemma 1(iii).
- `φ(T) = diag(u, u^{−1}, 1) ∈ G` by Lemma 2.
- A Lemma-3 element has finite order, so `I = 0` and `φ(g) = diag(w_g,1,1) ∈ G`.
- By Lemma 4 these elements generate `[[T]]`. ∎

**Scope.** Lemma 3 uses `GL_d(F_2) = SL_d(F_2)`. Over `F_q` with `q` odd, a transposition of two levels has determinant `−1` on the tower block, so the proof of Theorem B is specific to `F_2`. Corollary A holds over every field.

## 3. Compatibility with the finite models of the note
- The note's models (disk l.131–144) send `Σ_j f_j u^j ↦ Σ_j D_y(f_j) P^j`.
- Write `w_g = Σ_n e_{T^nA_n} u^n`. It goes to `Σ_n D_y(e_{T^nA_n}) P^n`.
- `e_{T^nA_n}(T^{m+n}y) = e_{A_n}(T^m y)` along the periodic word, and exactly one `A_n` contains each window of `X`. So column `m` has a single 1, in row `m + n_g(T^m y)`.
- So the image is the permutation `m ↦ m + n_g(T^m y)` of `Z/NZ`, i.e. the periodic approximation of `g`, once `k` exceeds the windows of `n_g`.
- The note's finite models of `G_X` therefore extend the periodic permutation models of `[[T]]`. This is the mechanism the note credits to Grigorchuk–Medynets.
