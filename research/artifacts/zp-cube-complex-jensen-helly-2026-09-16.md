# Median graphs of finite cube dimension have the Jensen–Helly property; every RAAG is of Rips type R (swarm-zaremsky-4-05, 2026-09-16)

Status: complete argument, UNREVIEWED (one swarm referee pass on 2026-09-16 re-derived §§1–9 line by line and found
no error; see the Referee section of `notes/zaremsky-4-05-raag-rips-complexes-contra-swarm-2026-09-16.md`). It proves hole
`raag-salvetti-covers-have-the-jensen-helly-property`, and more generally the property for the 1-skeleton of
every finite-dimensional CAT(0) cube complex. Through `jensen-helly-graphs-have-contractible-rips-complexes`
(UNREVIEWED; it rests on Zaremsky, arXiv:2410.11993v2, Theorem 3.1) this gives: for every finite simplicial graph
`Γ` with clique number `k ≥ 1`, `VR_t(A_Γ, V(Γ))` is contractible for every integer `t ≥ k(k+1) − 1`.

The proof has no case analysis on `Γ`. It works with hyperplane coordinates. The realization is the cube completion
sitting inside the box `[0,1]^H`, with the coordinate l^1 metric. The key observation is that every distance
function `d(x,·)` to a vertex `x` is *affine* on the whole box. So (J) and (H) become statements about a convex
polytope, together with one combinatorial move (the *unfolding*, Lemma U). The unfolding pushes a box point into
the cube complex without increasing any vertex distance.

## 0. Statements

Let `G` be a connected median graph with vertex set `V` and path metric `d`, and `H` its set of hyperplanes (§1).

- **Theorem A.** Suppose the cube dimension `k` of `G` (§2) is finite, `k ≥ 1`. Then `G` has the Jensen–Helly
  property of dimension `k` from `jensen-helly-graphs-have-contractible-rips-complexes`, realized by
  `(|X|, d_1)` of §2.
  - Bounded degree is not needed for Theorem A, only for the Rips theorem.
  - For the 1-skeleton of a CAT(0) cube complex of dimension `k`, the cube dimension is `k`. This uses the standard
    fact that such a complex is the cube completion of its median 1-skeleton (Chepoi 2000; Roller 1998;
    not re-fetched).
- **Corollary B.** Let `Γ` be a finite simplicial graph with clique number `k ≥ 1`. Then
  `VR_t(A_Γ, V(Γ))` is contractible for every integer `t ≥ k(k+1) − 1`. So every RAAG with its standard
  generating set is of Rips type R, answering Zaremsky Problem 4.5 affirmatively.

## 1. Median graph facts used

A graph is median if every triple of vertices has a unique median `m(a,b,c) ∈ I(a,b) ∩ I(b,c) ∩ I(a,c)`, where
`I(a,b)` is the set of vertices on geodesics from `a` to `b`. A vertex set `C` is convex if `I(a,b) ⊆ C` for all
`a, b ∈ C`. We use the following standard facts (Mulder 1980; Bandelt–Chepoi, "Metric graph theory and geometry:
a survey", 2008; not re-fetched).

- **(M1) Hyperplanes and halfspaces.** The Djoković–Winkler relation `Θ` on edges is an equivalence relation. Its
  classes are the *hyperplanes*. Removing the edges of a hyperplane `h` leaves exactly two components, the
  *halfspaces* `h^0` and `h^1`. Both are convex and nonempty. `Θ` has a metric definition:
  `uv Θ xy` iff `d(u,x) + d(v,y) ≠ d(u,y) + d(v,x)`.
- **(M2) Distance.** `d(u,v)` is the number of hyperplanes separating `u` and `v`. A geodesic crosses exactly
  these hyperplanes, each once.
- **(M3) Gates.** A convex set `K` is gated. For each `x` there is `x' ∈ K` with `d(x,y) = d(x,x') + d(x',y)` for all
  `y ∈ K`.
- **(M4) Convex subgraphs.** A convex set `K` induces a median graph. By the metric definition of `Θ`, the
  hyperplanes of `K` are the traces on `K` of the hyperplanes of `G` that cross `K`, meaning those with vertices of
  `K` on both sides.
- **(M5) Helly number 2 for convex sets** (proved here). Let `C_1, ..., C_m` be convex and pairwise
  intersecting. For three of them pick `a ∈ C_2 ∩ C_3`, `b ∈ C_1 ∩ C_3` and `c ∈ C_1 ∩ C_2`. The median
  `m(a,b,c)` lies in `I(b,c) ⊆ C_1`, in `I(a,c) ⊆ C_2` and in `I(a,b) ⊆ C_3`. So any three meet. Replace `C_1, C_2`
  by `C_1 ∩ C_2`. The new family is convex and still pairwise intersecting, so induction on `m` finishes.

Consequences.
- **Distinct hyperplanes induce distinct splits.** If `h ≠ h'` had the same halfspaces, an edge `uv` of `h` would be
  separated by both, so `d(u,v) ≥ 2` by (M2).
- **Hulls of finite sets are finite.** Let `S` be finite. A hyperplane not separating two points of `S` has `S` in
  one halfspace, which is convex, so it does not cross `hull(S)`. So the hyperplanes crossing `hull(S)` are the
  finitely many that separate points of `S`, and a vertex of `hull(S)` is determined by its sides of those
  hyperplanes (M2).

## 2. Coordinates, charges, cubes and the realization

Fix a base vertex `o`. Name the halfspaces so that `o ∈ h^0`, and put `c_v(h) = [v ∈ h^1]`. So `c_v ∈ {0,1}^H` has
finite support, and `d(u,v) = Σ_h |c_u(h) − c_v(h)|` by (M2).

**Charges.** Let `p ∈ [0,1]^H` differ from some `c_v` in finitely many coordinates. The *charge* of `p` on a
halfspace `A` of `h` is `q_A(p) = p_h` if `A = h^1`, and `1 − p_h` if `A = h^0`. So `q_A + q_{A*} = 1`, where `A*`
is the complementary halfspace, and `q_A(c_v) = [v ∈ A]`.

**Coordinate cubes.** A *coordinate cube* is a pair `(v, F)` with `v ∈ V` and `F ⊆ H` finite such that for every
`σ ∈ {0,1}^F` there is a vertex `v_σ` with `c_{v_σ} = c_v` off `F` and `c_{v_σ} = σ` on `F`.
- Its *hull* is `Q(v,F) = {p : p = c_v off F, p ∈ [0,1] on F}`, a face of the box `[0,1]^H`.
- The **cube dimension** of `G` is `k = sup |F|` over coordinate cubes.
- The **realization** is `|X| = ⋃ Q(v,F)` with the metric `d_1(p,p') = Σ_h |p_h − p'_h|`, which is finite.
- `V ↪ |X|` via `v ↦ c_v` is isometric by (M2).
- For a CAT(0) cube complex, the coordinate cubes of its 1-skeleton are the vertex sets of its cubes (standard,
  see §0). For RAAGs we bound the cube dimension directly in §9.

**Vertex distances are affine.** For `x ∈ V` and `p` as above, let `L_x(p) = d_1(c_x, p) = Σ_h q_{A_h(x)}(p)`,
where `A_h(x)` is the halfspace of `h` *not* containing `x`. So `L_x(p) = Σ_h (p_h if c_x(h) = 0; 1 − p_h if
c_x(h) = 1)`, which is affine in `p`.

For a finitely supported probability measure `μ` on `V`, put `w_h = μ(h^1)`, so `q_A(w) = μ(A)`. Then

`L_x(w) = Σ_h μ(A_h(x)) = Σ_y μ(y) · #{h separating x, y} = ∫ d(x,y) dμ(y)`. (2.1)

**Empty quadrants.** A pair `(A,B)` is an *empty quadrant* if `A` and `B` are halfspaces of distinct hyperplanes
and `A ∩ B = ∅`. A point `p` satisfies **(*)** if `min(q_A(p), q_B(p)) = 0` for every empty quadrant `(A,B)`.

## 3. Lemma C (points of |X|; `G` finite)

**Lemma C.** Let `G` be finite. Then `p ∈ [0,1]^H` lies in `|X|` iff `p` satisfies (*). If `p` satisfies (*), then
`p ∈ Q(v,F)` with `F = {h : 0 < p_h < 1}`.

*Proof.* (⇒) Let `p ∈ Q(v,F)` and let `(A,B)` be an empty quadrant of `h ≠ h'`, with both charges positive.
- If `h, h' ∈ F`, some corner `v_σ` has the sides `A` and `B`, so `v_σ ∈ A ∩ B`.
- If `h ∈ F` and `h' ∉ F`, then `p_{h'} ∈ {0,1}` and `q_B(p) > 0` give `q_B(p) = 1`. So every corner lies in `B`,
  and some corner lies in `A`. The case `h ∉ F`, `h' ∈ F` is symmetric.
- If `h, h' ∉ F`, then `v ∈ A ∩ B`.

Each case contradicts `A ∩ B = ∅`.

(⇐) Let `F = {h : 0 < p_h < 1}`. For `h ∉ F` let `A_h` be the halfspace with `q_{A_h}(p) = 1`. Fix
`σ ∈ {0,1}^F` and consider the family `𝓕_σ = {A_h : h ∉ F} ∪ {h^{σ(h)} : h ∈ F}`. It has one halfspace per
hyperplane, and every member has positive charge. By (*), no two members form an empty quadrant, so they pairwise
intersect. By (M5) there is a vertex in all of them. It is unique by (M2), since it lies on a prescribed side of
every hyperplane. Call it `v_σ`. Then `c_{v_σ} = p` off `F` and `c_{v_σ} = σ` on `F`. So for any fixed `σ_0`,
`(v_{σ_0}, F)` is a coordinate cube whose hull contains `p`. ∎

## 4. Lemma U (unfolding)

**Lemma U.** Let `G` be finite, `p ∈ E := [0,1]^H`, and `(A,B)` an empty quadrant of `h ≠ h'` with
`s := min(q_A(p), q_B(p)) > 0`. Define `p'` by `q_A(p') = q_A(p) − s` and `q_B(p') = q_B(p) − s`, leaving the other
coordinates unchanged. Then:
1. `p' ∈ E`.
2. For every `x ∈ V`: `L_x(p') = L_x(p) − 2s` if `x ∈ A* ∩ B*`, and `L_x(p') = L_x(p)` otherwise.
3. `A* ∩ B* ≠ ∅`.
4. `Σ_h p'_h² ≤ Σ_h p_h² + 6s`.

*Proof.* (1) holds because `s ≤ q_A(p), q_B(p)`.

(2) Only the charges on `A, A*, B, B*` change: `A` and `B` lose `s`, and `A*` and `B*` gain `s`. The vertex `x` is
not in `A ∩ B`, so there are three cases.
- If `x ∈ A`, then `x ∈ B*`. The halfspaces of `h, h'` not containing `x` are `A*` (gains `s`) and `B` (loses `s`),
  so the net change is 0.
- If `x ∈ B`, the same holds by symmetry.
- If `x ∈ A* ∩ B*`, the halfspaces not containing `x` are `A` and `B`, so `L_x` changes by `−2s`.

(3) `A ∩ B = ∅` gives `B ⊆ A*`. If also `A* ∩ B* = ∅`, then `A* ⊆ B`, so `A* = B` and `h, h'` induce the same split.
This contradicts §1.

(4) Two coordinates change by `s ≤ 1`, and `(y ± s)² − y² ≤ 2s + s² ≤ 3s` for `y ∈ [0,1]`. ∎

## 5. Lemma J (Jensen barycentres)

**Lemma J.** For every finitely supported probability measure `μ` on `V` there is `b ∈ |X|` with
`d_1(x,b) ≤ ∫ d(x,y) dμ(y)` for all `x ∈ V`.

*Proof, `G` finite.* Let `D = {c ∈ E : L_x(c) ≤ L_x(w) ∀ x ∈ V}`. It is a compact polytope containing `w`. Let `b`
minimize the linear function `Φ = Σ_{x ∈ V} L_x` over `D`. Suppose `b` violates (*). Lemma U gives `b' ∈ E` with
`L_x(b') ≤ L_x(b)` for all `x`, so `b' ∈ D`, and `Φ(b') ≤ Φ(b) − 2s < Φ(b)`. That contradicts minimality. So `b`
satisfies (*), hence `b ∈ |X|` by Lemma C, and `d_1(x,b) = L_x(b) ≤ L_x(w) = ∫ d(x,y) dμ` by (2.1).

*Proof, `G` arbitrary.* Let `K = hull(supp μ)`, which is finite by §1, and `H(K)` the hyperplanes crossing `K`. Off
`H(K)` all of `K` has a common coordinate vector `c_K`.
- By (M4), `K` is a finite median graph with hyperplanes `H(K)`. Its coordinate cubes, extended by `c_K` off `H(K)`,
  are coordinate cubes of `G`.
- The finite case gives `b_K ∈ |X_K|` with `d_1(x,b_K) ≤ ∫ d(x,y) dμ` for `x ∈ K`. Let `b = b_K` on `H(K)` and `c_K`
  elsewhere. Then `b ∈ |X|`.
- Let `x ∈ V` with gate `x' ∈ K` (M3). A hyperplane separating `x` from `x'` cannot cross `K`. Otherwise pick
  `y ∈ K` on the side of `x`: the geodesic `x → x' → y` would cross it twice, contradicting (M2).
- Hence `c_x = c_{x'}` on `H(K)`, and `c_x` differs from `c_K` in exactly `d(x,x')` coordinates off `H(K)`.
- Therefore `d_1(x,b) = d(x,x') + d_1(x',b_K) ≤ d(x,x') + ∫ d(x',y) dμ = ∫ d(x,y) dμ`, using (M3) for `y ∈ K`. ∎

## 6. Lemma Rt (a retraction of the box onto the cube complex; `G` finite)

For `c ∈ E` let `D_c = {c' ∈ E : L_x(c') ≤ L_x(c) ∀ x ∈ V}` and `Ψ(c') = Σ_x L_x(c') + (1/8) Σ_h c'_h²`. The set
`D_c` is a nonempty compact polytope and `Ψ` is strictly convex, so `r(c) := argmin_{D_c} Ψ` is well defined.

**Lemma Rt.**
- (a) `r(c) ∈ |X|` and `L_x(r(c)) ≤ L_x(c)` for all `x ∈ V`.
- (b) `r(p) = p` for `p ∈ |X|`.
- (c) `r : E → |X|` is continuous.

*Proof.*

(a) If `r(c)` violated (*), Lemma U would produce a point of `D_c` with `Ψ` smaller by at least
`2s − 6s/8 > 0`. So (*) holds, and Lemma C applies.

(b) Let `p ∈ Q(v,F)` with `F = {h : 0 < p_h < 1}` and corners `v_σ` (Lemma C), and let `c' ∈ D_p`.
- For `σ` and its antipode `σ̄`: `L_{v_σ}(p) + L_{v_σ̄}(p) = |F|`, and
  `L_{v_σ}(c') + L_{v_σ̄}(c') = |F| + 2 Σ_{h ∉ F} |c'_h − p_h|`. So `c' = p` off `F`.
- Put `ℓ_σ(y) := Σ_{g ∈ F} |σ_g − y_g|` for `y ∈ [0,1]^F`. Since `c' = p` off `F`, `L_{v_σ}(c') = ℓ_σ(c'|_F)` and
  `L_{v_σ}(p) = ℓ_σ(p|_F)`, so `ℓ_σ(c') ≤ ℓ_σ(p)` for all `σ`.
  Summing over the `2^{|F|}` corners, each `y_g ∈ [0,1]` contributes `2^{|F|−1}` regardless of its value. So
  `Σ_σ ℓ_σ(c') = Σ_σ ℓ_σ(p)`, and all these inequalities are equalities.
- For `σ` and `σ^g` (flip at `g`): `ℓ_σ − ℓ_{σ^g} = (1 − 2σ_g)(2y_g − 1)`. Equality at `y = c'` and `y = p` gives
  `c'_g = p_g`.

So `D_p = {p}` and `r(p) = p`.

(c) Write `D_c = {y ∈ R^H : Ãy ≤ β(c)}`, where the rows of `Ã` are the linear parts `a_x` of the `L_x` together with
the box rows, and `β(c) = (a_x · c)_x ⊕ (1,...,1) ⊕ (0,...,0)` is linear in `c`.
- **Hoffman's error bound** (A. J. Hoffman, J. Res. Nat. Bur. Standards 49 (1952) 263–265; not re-fetched): there
  is `κ = κ(Ã)` with `dist(y, {Ãy' ≤ β}) ≤ κ ‖(Ãy − β)_+‖` for all `y` and all `β` making the set nonempty.
- Let `c_n → c` and `u ∈ D_c`. Then `(Ãu − β(c_n))_+ ≤ |β(c) − β(c_n)|`, so there are `u_n ∈ D_{c_n}` with
  `u_n → u`.
- Suppose `r(c_n) ↛ r(c)`. By compactness a subsequence converges to some `q ≠ r(c)`. Since `D_c` is closed,
  `q ∈ D_c`.
- Take `u_n ∈ D_{c_n}` with `u_n → r(c)`. Then `Ψ(r(c_n)) ≤ Ψ(u_n)`, and in the limit `Ψ(q) ≤ Ψ(r(c))`. By
  uniqueness `q = r(c)`, a contradiction. ∎

**Corollary Rt.** Let `G` be finite.
1. `|X|` is contractible, as a retract of `E`.
2. For vertices `z_i` and reals `ρ_i` (`i ∈ I`, finite), put `B_I = {p ∈ |X| : d_1(z_i,p) ≤ ρ_i ∀ i ∈ I}` and
   `P_I = {c ∈ E : L_{z_i}(c) ≤ ρ_i ∀ i ∈ I}`. Then `r(P_I) = B_I`. So `B_I ≠ ∅` iff `P_I ≠ ∅`, and a nonempty
   `B_I` is a retract of the convex set `P_I`, hence contractible.

The proof of (2) uses only `L_{z_i}(r(c)) ≤ L_{z_i}(c)` and `r|_{B_I} = id`. It needs the centres to be vertices.

## 7. Lemma H (Helly number `k+1`)

**Lemma H.** Let `B_i = B(z_i, ρ_i) ⊆ |X|`, `i = 0..m`, with `z_i ∈ V`. If every subfamily of at most `k+1` members
has a common point, all members have a common point.

*Proof, `G` finite.*
- **Triangulation.** The faces of the box `E` form a polyhedral complex, and `|X|` is a subcomplex, since each
  `Q(v,F)` and each of its faces is a face of `E` inside `|X|`. Refine it by the finite arrangement of affine
  hyperplanes `{L_{z_i} = ρ_i}`. The cells `Q ∩ C` (`Q` a face of `E` in `|X|`, `C` a closed cell of the arrangement)
  form a polyhedral complex with support `|X|`, and each `B_i` is a union of cells closed under faces. A barycentric
  subdivision gives a simplicial complex `Δ` of dimension `≤ k` in which every `B_i`, and hence every `B_I`, is a
  subcomplex.
- **Setup.** Suppose the conclusion fails. Take a minimal subfamily with empty intersection, say `B_0..B_n`. All
  proper subfamilies meet, and by hypothesis `n + 1 ≥ k + 2`. Let `U = B_0 ∪ ... ∪ B_n`.
- **Nerve.** Every nonempty `B_I` is contractible by Corollary Rt. By the nerve theorem for simplicial complexes
  covered by subcomplexes (Björner, Handbook of Combinatorics 1995, Theorem 10.6; Borsuk 1948; not re-fetched), `U`
  is homotopy equivalent to the nerve, which is `∂Δ^n ≅ S^{n−1}`. So `H^{n−1}(U; Z) ≅ Z` with `n − 1 ≥ k ≥ 1`.
- **If `n − 1 ≥ k + 1`.** `H^{n−1}(U) = 0`, because `U` is a complex of dimension `≤ k`.
- **If `n − 1 = k`.** The exact sequence of the pair `(|X|, U)` contains `H^k(|X|) → H^k(U) → H^{k+1}(|X|, U)`. Here
  `H^k(|X|) = 0` (contractible, `k ≥ 1`) and `H^{k+1}(|X|,U) = 0` (no `(k+1)`-simplices), so `H^k(U) = 0`.

Either case is a contradiction.

*Proof, `G` arbitrary.* For each subfamily `T` of at most `k+1` members choose a witness `p_T ∈ Q(v_T, F_T)`.
- Let `S` consist of the centres `z_i` and the `2^{|F_T|}` corners of all these cubes, and `K = hull(S)`, which is
  finite.
- Restricting coordinates to `H(K)` embeds each `p_T` into `|X_K|`. It does not change `d_1(z_i, p_T)`: `z_i` and
  the corners share `c_K` off `H(K)`.
- `K` has cube dimension `≤ k` (§5). By the finite case, all `B_i ∩ |X_K|` meet at some `q`. (The finite-case
  proof uses only `dim |X_K| ≤ k` and `k ≥ 1`, so it applies with the `k` of `G` even if `K` has smaller cube
  dimension.) Extending `q` by `c_K`
  gives a point of `|X|` with the same distances to the `z_i`. ∎

## 8. Lemma R and proof of Theorem A

**Lemma R.** Let `p ∈ Q(v,F)` with `|F| ≤ k`. Round each `p_h`, `h ∈ F`, to the nearest of 0 and 1 to get a corner
`σ`. Then `d_1(p, v_σ) = Σ_{h ∈ F} |p_h − σ_h| ≤ |F|/2 ≤ k/2`. ∎

*Theorem A.* `(|X|, d_1)` contains `(V,d)` isometrically (§2). (J) is Lemma J, (H) is Lemma H and (R) is Lemma R. ∎

## 9. RAAGs: proof of Corollary B

Let `G_Γ` be the Cayley graph of `(A_Γ, V(Γ))`. It is the 1-skeleton of the universal cover of the Salvetti
complex, a CAT(0) cube complex (Charney–Davis 1995), so it is a median graph (Chepoi 2000, theorem number not re-checked; Roller
1998). Both citations are standard and were not re-fetched; the same standard fact is stated in Hulbert–Zaremsky,
arXiv:2608.25614v1, §4 (read 2026-09-16). Its degree is `2|V(Γ)|`.

**The cube dimension of `G_Γ` is at most the clique number `k`.** Let `(g, F)` be a coordinate cube, taking the base
corner `g` (any corner can be the base). For `h ∈ F`, flipping `h` gives a vertex at distance 1 from `g` (M2), namely
`g a_h` for some `a_h ∈ V(Γ)^{±1}`. Distinct `h` give distinct neighbours, hence distinct labels `a_h`.
- For `h ≠ h'`, let `g_1`, `g_2`, `g_{12}` be the corners flipping `h`, `h'` and both. By (M2),
  `d(g, g_{12}) = d(g_1, g_2) = 2`, so `g, g_1, g_{12}, g_2` is an induced 4-cycle. Write `g_1 = g a`, `g_{12} = g_1 b`,
  `g_2 = g_{12} c`, `g = g_2 d` with `a = a_h` and `b, c, d ∈ V(Γ)^{±1}`, so `abcd = 1`.
- **Squares are visible** (Hulbert–Zaremsky, arXiv:2608.25614v1, Observation 4.2, read 2026-09-16; the argument is
  short, so we repeat it). The homomorphism `A_Γ → Z` sending `a` to `1`, `a^{−1}` to `−1` and every other generator
  to `0` shows that one of `b, c, d` is `a^{−1}`. Now `b = a^{−1}` gives `g_{12} = g`, and `d = a^{−1}` gives
  `g_2 = g d^{−1} = g_1`; so `c = a^{−1}`. The same argument for `b` gives `d = b^{−1}`. Hence `[a,b] = 1` and
  `g_2 = g b`, that is, `b = a_{h'}`.
- `a_h` and `a_{h'}` are powers of distinct generators: `b = a^{−1}` gives `g_{12} = g`, and `b = a` gives
  `g_2 = g_{12} a^{−1} = g_1`.
- Distinct non-adjacent generators `u, v` do not commute: killing every other generator defines a homomorphism
  `A_Γ → F(u,v)` (each defining relator `[x,y]` has `x` or `y` outside `{u,v}`, since `u, v` are not adjacent, so it
  maps to `1`), and `[u,v] ≠ 1` in the free group.
- So the generators underlying `a_h`, `h ∈ F`, are pairwise distinct and pairwise adjacent in `Γ`: a clique of size
  `|F|`, and `|F| ≤ k`.

By Theorem A, `G_Γ` has the Jensen–Helly property of dimension `k' ≤ k`, hence of dimension `k`: Helly number
`k'+1` implies `k+1`, and `k'/2 ≤ k/2`. Then `jensen-helly-graphs-have-contractible-rips-complexes` gives
`VR_t(A_Γ, V(Γ))` contractible for every integer `t ≥ k(k+1) − 1`. ∎

**Remarks.**
- The same argument applies to any group acting simply transitively on the vertices of a locally finite CAT(0) cube
  complex of dimension `k`, with the edge labels as generators. The Cayley graph is then the median 1-skeleton.
- In particular it applies to right-angled Coxeter groups with standard generators (Davis complex). There, too,
  a 4-cycle `g, gs, gt, gst` forces `s,t` to commute, so the cube dimension is the clique number.
- The bound `k(k+1) − 1` is what the criterion-based proof yields. Hulbert–Zaremsky (arXiv:2608.25614v1, §1) call
  `t ≥ k` "a natural prediction". That is not addressed here.

## 10. Model tests and computations

**Model tests.**
- `Z^n`: `|X| = R^n` with l^1, and Lemma J yields a point `b` with `d_1(x,b) ≤ ∫ d_1(x,y) dμ`. The mean works too.
- Trees: Lemma C says a charge vector with no charged empty quadrant is a point on an edge. The Φ-minimizer is a
  tree barycentre.
- The counterexample in the Attempts of `raag-salvetti-covers-have-the-jensen-helly-property` is `Z^2 * Z`, with mass
  1/2 one step behind the cut vertex `g` and mass 1/2 at `y_0` with `d(g,y_0) = 10`.
  - `w` has charge 1/2 on the pendant side of the pendant edge's hyperplane and on the `y_0`-side of each of 10 plane
    hyperplanes. The pendant side and each `y_0`-side form an empty quadrant, so `w ∉ |X|`.
  - Let `x_0` be the pendant vertex. Any `b` from Lemma J has `d_1(x_0,b) ≤ 5.5` and `d_1(y_0,b) ≤ 5.5`, with
    `d(x_0,y_0) = 11`. So both are equalities. `b` cannot lie on the pendant edge (there `d_1(y_0,b) ≥ 10`), so
    `d_1(g,b) = 4.5`. This is the value recorded there.
- **Sharpness of `k+1`.** In `R^3` with l^1, the balls centred at `(0,−1,−1)`, `(−2,0,−2)`, `(−1,1,0)` and
  `(1,1,−2)` with offsets `2.5, 2.5, 2.5, 2` have gap `0.375`. Enlarging the radii by the largest 3-subfamily value,
  every 3 balls meet and the 4 do not. So Helly number 3 fails in dimension 3.

**Computations** (`experiments/zaremsky-4-05-jensen-cube-2026-09-16/`, scipy HiGHS LPs, single-threaded, each run
under 10 minutes).
- `jtest.py`, `jtest2.py`: (J) feasibility over all maximal cubes of hulls of random supports in the Salvetti covers
  of `P4` and `K_1 * P4`. No failures.
- `jhelly.py`, three tests on hulls of random centres in Salvetti covers of `P4`, `C5`, `K_1*P4`,
  `triangle+pendant`, `K4−path` and `K_2*P4` (`k = 4`):
  - (E) the box minimum of `max_i (L_{z_i} − ρ_i)` equals the minimum over `|X|`, as Corollary Rt predicts;
  - (U) the LP minimizer of `Φ` over `D` has no charged empty quadrant, as in the proof of Lemma J;
  - (H) the full minimum equals the maximum over `(k+1)`-subfamilies.
  - All counts were zero: `box_mismatch 0`, `unfold_worst 0.0`, `helly_fail 0`, over 40 trials each at `R=3` and 30
    or 8 trials at `R=2`.
- `jhelly_splits.py`: Helly number `κ+1` for split systems (any multiset of splits of `m` centres), where `κ` is the
  largest pairwise-incompatible family of splits. Hill-climbing `ρ` found no failure, for `m = 4, 5, 6`. The same
  search found positive gaps for `κ`-subfamilies at `κ = 3, 4`, so it does find Helly failures. The R^3 example is
  its sanity check.
- `jhelly_adv.py`: an adversarial search directly on Salvetti-cover hulls. No failures, and it is too weak to find
  failures even where they exist, so it is not evidence.

## 11. Where a referee should look

1. **Lemma Rt(c): continuity of `r`.** It uses Hoffman's bound for the lower semicontinuity of `c ↦ D_c`, plus
   uniqueness of the minimizer. Continuity is needed only to make `B_I` a retract of `P_I` (contractibility). The
   emptiness equivalence `B_I ≠ ∅ ⟺ P_I ≠ ∅` needs only Lemma Rt(a).
2. **Lemma H.** The common triangulation and the nerve theorem for subcomplexes.
3. **Standard facts not re-fetched.** The median graph facts (M1)–(M4), and that Salvetti covers are CAT(0) with
   median 1-skeleton (also stated as standard in arXiv:2608.25614v1, §4). The cube-dimension bound of §9 is
   self-contained.
4. **Upstream.** The Rips conclusion rests on the UNREVIEWED node
   `jensen-helly-graphs-have-contractible-rips-complexes`. Its only import is Zaremsky's Theorem 3.1, re-read verbatim
   from arXiv:2410.11993v2 (dated August 14, 2025) on 2026-09-16.
