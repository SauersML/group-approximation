# sk-free-3: the conjugacy problem of G_X, part 1 — transvection conjugacy is full-group equivalence (2026-09-13)

Lane sk-free-3 (free lane). Plan: `research/artifacts/sk-free-3-plan-2026-09-13.md` (9dae89d385). Part 2 holds the construction and the degree theorem.

## 0. Setting and notation (as in the note, main 9047d0d3c9)
- X ⊆ A^Z is an infinite minimal subshift, T the shift.
- R = LC(X,F_2)⋊_T Z, with (fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}, so u 1_U u^{−1} = 1_{TU}.
- G = G_X = EL_3(R).
- For clopen U, write 1_U ∈ LC(X,F_2).
- The topological full group [[T]] consists of the homeomorphisms γ of X of the form γ(x) = T^{n(x)}x with n: X → Z continuous.
- C(X,Z) denotes the continuous integer-valued functions.

## 1. Lemma K
**Lemma K.** For clopen sets A, B ⊆ X the following are equivalent:
- (a) e_13(1_A) and e_13(1_B) are conjugate in G_X;
- (b) 1_A − 1_B = g∘T − g for some g ∈ C(X,Z);
- (c) there is γ ∈ [[T]] with γ(A) = B.

Equivalently, (b) says [1_A] = [1_B] in K^0(X,T) = C(X,Z)/(1−T_*)C(X,Z).

### 1.1 (c) ⇒ (a)
Let U_k = {n = k}, a finite clopen partition, and put w = Σ_k 1_{γU_k} u^k ∈ R.
- **w intertwines γ.** On γU_k we have γ^{−1} = T^{−k}, so for f ∈ LC(X,F_2): w f = Σ_k 1_{γU_k}(f∘T^{−k})u^k = (f∘γ^{−1}) w.
- **w is a unit with inverse w′ = Σ_k 1_{U_k} u^{−k}.**
  - w w′ = Σ_{k,l} 1_{T^kU_k} 1_{T^kU_l} u^{k−l} = Σ_k 1_{γU_k} = 1, since T^kU_k ∩ T^kU_l = ∅ for k ≠ l and the sets γU_k partition X.
  - w′ w = Σ_{k,l} 1_{U_k} 1_{T^{l−k}U_l} u^{l−k}. A point of U_k ∩ T^{l−k}U_l would be x = T^{l−k}y with y ∈ U_l, so γx = T^k x = T^l y = γy, hence x = y and k = l. So w′ w = Σ_k 1_{U_k} = 1.
- **Conjugation.** Hence w 1_A w^{−1} = 1_{γA} = 1_B.
- **A diagonal conjugator inside G.** In characteristic 2, e_12(c)e_21(c^{−1})e_12(c) = [[0,c],[c^{−1},0]], and multiplying by e_12(1)e_21(1)e_12(1) = [[0,1],[1,0]] gives diag(c,c^{−1}). So diag(c,c^{−1},1) ∈ G and diag(1,c,c^{−1}) ∈ G for every unit c. Then k := diag(w,w^{−1},1)·diag(1,w^{−1},w) = diag(w,w^{−2},w) ∈ G.
- **Conclusion.** Since diag(a,b,c) e_13(r) diag(a,b,c)^{−1} = e_13(a r c^{−1}), we get k e_13(1_A) k^{−1} = e_13(w 1_A w^{−1}) = e_13(1_B).

### 1.2 (b) ⇒ (c) (Kakutani–Rokhlin towers)
Let f = 1_A − 1_B = g∘T − g.
- **Base.** Choose a nonempty clopen Z on which g is constant. By minimality the return time r_Z(z) = min{n ≥ 1 : T^n z ∈ Z} is finite, continuous and bounded.
- **Towers.** Partition Z into the clopen sets Z_{h,β}, where h = r_Z(z) and β records, for j < h, whether T^j z ∈ A and whether T^j z ∈ B. The levels T^jZ_{h,β}, 0 ≤ j < h, partition X, and each level lies inside A or X∖A, and inside B or X∖B.
- **Equal counts.** For z ∈ Z_{h,β}, Σ_{j<h} f(T^j z) = g(T^h z) − g(z) = 0, because T^h z ∈ Z and g is constant on Z. So each tower has as many A-levels as B-levels, and so as many non-A levels as non-B levels.
- **γ.** Choose a bijection σ of {0,…,h−1} sending A-levels to B-levels and non-A levels to non-B levels, and set γ = T^{σ(j)−j} on T^jZ_{h,β}. Then γ permutes the levels, γ ∈ [[T]], and γ(A) = B.

Credit: this is the standard Kakutani–Rokhlin tower argument used in the Glasner–Weiss and Giordano–Putnam–Skau comparison of clopen sets in minimal Cantor systems. The exact locator is NOT checked (VERIFY); the proof above is self-contained.

### 1.3 (a) ⇒ (b), route 1: finite models and a Livšic loop argument
- **Bounds.** Let k ∈ G with k e_13(1_A) k^{−1} = e_13(1_B), and write the entries of k and k^{−1} as Σ_j f_j u^j. Let λ bound |j| over all these entries, and let ρ bound the window radius of all f_j, 1_A and 1_B. Fix ℓ ≥ ρ + 4λ + 1 and L = 2ℓ+1.
- **Periodic model.** Let y be N-periodic with every window y[t−ℓ, t+ℓ] in L(X). For f of radius ≤ ℓ let D(f) = diag(f(y^{(t)}))_{t∈Z/N}, where f(y^{(t)}) is f at any point with window y[t−ℓ,t+ℓ]; this is well defined. Let P be the cyclic shift with P D(f) P^{−1} = D(f∘T^{−1}) for f of radius ≤ ℓ−1.
- **Multiplicativity.** The map φ(Σ_j f_j u^j) = Σ_j D(f_j) P^j is additive. It satisfies φ(fu^i)φ(f′u^j) = D(f)D(f′∘T^{−i})P^{i+j} = φ((fu^i)(f′u^j)) whenever f′ has radius ≤ ℓ−|i|. Every product in the identities k·(I+E_13 1_A) = (I+E_13 1_B)·k and k k^{−1} = I stays within these bounds.
- **Rank equality.** K = φ(k) ∈ GL_{3N}(F_2) conjugates I + E_13 D(1_A) to I + E_13 D(1_B). So rank D(1_A) = rank D(1_B), which says Σ_{t∈Z/N} f(y^{(t)}) = 0 for f = 1_A − 1_B.
- **Loops give models.** Fix x ∈ X; its forward orbit is dense by minimality. Suppose x[a,a+L) = x[b,b+L) with a < b, and let y be the (b−a)-periodic word with y[0,b−a) = x[a,b).
  - Then y[0, b−a+L) = x[a, b+L), so every window of y of length L lies in L(X) and y is an admissible model.
  - For ℓ ≤ t < ℓ + (b−a), the window y[t−ℓ,t+ℓ] equals x[a+t−ℓ, a+t+ℓ], so f(y^{(t)}) = f(T^{a+t}x).
  - Writing S(k) = Σ_{i<k} f(T^i x), the loop sum is S(b+ℓ) − S(a+ℓ). So S(a+ℓ) = S(b+ℓ) whenever the L-windows of x at a and b agree.
- **The transfer function.** Define G(v) = S(a+ℓ) for any a ≥ 0 with x[a,a+L) = v ∈ L_L(X); it is well defined and defined everywhere by density. Put g(z) = G(z[−ℓ,ℓ]) ∈ C(X,Z). For k ≥ ℓ, g(T^kx) = S(k), so g(T^{k+1}x) − g(T^kx) = f(T^kx). Both sides are continuous and agree on the dense set {T^kx : k ≥ ℓ}, so g∘T − g = f.

### 1.4 (a) ⇒ (b), route 2 (cross-check through K_0)
- **Module isomorphism.** Left multiplication by N_A = E_13 1_A on the right module R^3 has image (1_A R, 0, 0)^T ≅ 1_A R. A conjugator k maps im N_A onto im N_B, so 1_A R ≅ 1_B R and [1_A] = [1_B] in K_0(R).
- **Coinvariants.** The node `subshift-crossed-product-k0-is-coinvariant-group` (PASS at group level, sk-verify-3) identifies K_0(R) ≅ C(X,Z)/(1−T_*)C(X,Z) with [1_U] ↦ [1_U]. So 1_A − 1_B = h − h∘T^{−1} with h ∈ C(X,Z), and g = h∘T^{−1} gives (b).

## 2. Upper bound
**Lemma U.** CP(G_X) ≤_T L(X)′.

Proof: (g,h) is a yes-instance iff ∃ word k with k g k^{−1} h^{−1} = 1 in G_X. This is Σ^0_1 relative to WP(G_X), and WP(G_X) ≡_T L(X) by the note's §3 corollary (node `subshift-elementary-group-word-problem-degree`). Every Σ^0_1(S) set is computable from S′. Also WP ≤_T CP, since g = 1 iff g is conjugate to 1.

## 3. Remarks
- **Corollary K.** For every X, the [[T]]-equivalence problem for clopen sets (equivalently the coboundary problem for 1_A − 1_B) many-one reduces to CP(G_X). The cylinder products e_13(Π_t u^{−t}e_{v_t}u^t) have words computable from v by eq. (1) of the note, and e_13 is additive, so words for e_13(1_A) are computable from a list of cylinders for A.
- **Group-theoretic reading.** Lemma K says that the root-transvection conjugacy classes {e_13(1_A)}/∼ are exactly the classes [1_A] ∈ K^0(X,T) with 0 ≤ [1_A] ≤ [1]. So the dimension group of Giordano–Putnam–Skau is visible inside G_X by conjugation. This is a possible input for isomorphism rigidity; that lane is sk-iso-rigidity, not this one.
- **Other fields.** Over F_q the same proof works: the rank argument is unchanged, and the Whitehead identity uses signs. Over any field only the idempotents 1_A enter.
