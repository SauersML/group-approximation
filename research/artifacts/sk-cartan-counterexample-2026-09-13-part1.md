# sk-cartan-counterexample, part 1: the corner firewall, recognition of Z-action groupoids, and a reduction

Lane sk-cartan-counterexample, 2026-09-13 (wave 9, ROSTER-G). The brief offers two routes around the open claim
`subshift-crossed-product-algebraic-cartans-are-conjugate`:
- (a) find a ring isomorphism R_X ≅ R_Y between strongly orbit equivalent, non-flip-conjugate subshifts of equal
  complexity growth;
- (b) show that every effective groupoid model of R_X is a transformation groupoid.

Status. Theorem A, Corollaries A′ and B, Lemma C and Theorem D are established with complete proofs below, and are
UNREVIEWED (queued with sk-verify-7). The open claim stays OPEN. Novelty check: a grep of main only; Theorem A and
Lemma C are folklore-level, and the credit is recorded at each item.

## 0. Setting and conventions
- (X,T) is a minimal Cantor system with no periodic points. K^0(X,T) = C(X,Z)/{f − f∘T^{-1}}.
- R_X = LC(X,F_2) ⋊_T Z, with diagonal D_X = LC(X,F_2) and transformation groupoid 𝒢_X = Z ⋉ X.
- For a nonempty clopen U ⊆ X:
  - r_U(u) = min{k ≥ 1 : T^k u ∈ U} is continuous and bounded (minimality and compactness);
  - T_U = T^{r_U} is the induced homeomorphism of U, again minimal.
- The tower over a minimal Cantor system (Z,σ) with continuous roof r: Z → {1,2,…} is
  X_r = {(z,i) : z ∈ Z, 0 ≤ i < r(z)}, with T_r(z,i) = (z,i+1) if i+1 < r(z) and T_r(z,i) = (σz,0) otherwise.
  The map (u,i) ↦ T^i u conjugates the tower over (U,T_U) with roof r_U onto (X,T).
- Induction. ι_U: C(X,Z) → C(U,Z), ι_U(f)(u) = Σ_{0≤i<r_U(u)} f(T^i u).
  - Telescoping gives ι_U(f − f∘T^{-1}) = g∘T_U − g with g = f∘T^{-1}|_U, so ι_U descends to K^0(X,T) → K^0(U,T_U).
  - ι_U[1_X] = [r_U] and ι_U[1_U] = [1_U].

## 1. Theorem A: cohomologous roofs give conjugate towers
**Theorem A.** Let (Z,σ) be an infinite minimal Cantor system and r, r′: Z → {1,2,…} continuous with
r′ − r = h − h∘σ for some continuous h: Z → Z. Then (X_r,T_r) and (X_{r′},T_{r′}) are topologically conjugate.

**Proof.** Write p = (z,0) ∈ X_r and p′ = (z,0) ∈ X_{r′} for the base points over z.
- Partial sums. R_k(z) = Σ_{0≤j<k} r(σ^j z) for k ≥ 0, and R_k(z) = −Σ_{k≤j<0} r(σ^j z) for k < 0. Define R′_k from r′
  in the same way. Summing r′ − r = h − h∘σ gives, for every k ∈ Z,
  R′_k(z) − R_k(z) = h(z) − h(σ^k z).
- Representatives. Every point of X_r is T_r^n(z,0) for some z ∈ Z and n ∈ Z. Because σ has no periodic points, two
  representatives (z,n) and (z″,n″) give the same point iff z″ = σ^k z and n = n″ + R_k(z) for one k ∈ Z.
- Definition. Put Φ(T_r^n(z,0)) = T_{r′}^{n+h(z)}(z,0).
- Well defined. The representative (σ^k z, n − R_k(z)) is sent to
  T_{r′}^{n − R_k(z) + h(σ^k z)}(σ^k z,0) = T_{r′}^{n − R_k(z) + h(σ^k z) + R′_k(z)}(z,0) = T_{r′}^{n+h(z)}(z,0),
  using (σ^k z,0) = T_{r′}^{R′_k(z)}(z,0) and the partial-sum identity.
- Equivariance. Φ∘T_r = T_{r′}∘Φ, by definition.
- Inverse. Ψ(T_{r′}^n(z,0)) = T_r^{n−h(z)}(z,0) is well defined by the same computation with the roles of r and r′
  exchanged (r − r′ = (−h) − (−h)∘σ), and Ψ∘Φ = id, Φ∘Ψ = id.
- Continuity. Partition Z into clopen sets Z_c on which r and h are constant. On each clopen piece
  {T_r^i(z,0) : z ∈ Z_c} with i < r|_{Z_c}, the map is z ↦ T_{r′}^{i+h|_{Z_c}}(z,0), which is continuous. The same holds
  for Ψ. ∎

Credit: this is the discrete form of the folklore fact that cohomologous roof functions give conjugate suspension
flows. Towers and induced systems go back to Kakutani; for Cantor minimal systems see Herman–Putnam–Skau (1992) and
Glasner–Weiss (1995).

**Corollary A′ (induced systems with matching unit class).** Let (X,T) and (Y,S) be infinite minimal Cantor systems,
U ⊆ X and V ⊆ Y nonempty clopen, and θ: U → V a homeomorphism with θ∘T_U = S_V∘θ and θ_*ι_U[1_X] = ι_V[1_Y] in
K^0(V,S_V). Then (X,T) ≅ (Y,S).
- If instead θ∘T_U = S_V^{-1}∘θ and θ_*ι_U[1_X] = ι_V[1_Y], then (X,T) ≅ (Y,S^{-1}).

**Proof.** The tower over (V,S_V) with roof r_V is conjugate through θ to the tower over (U,T_U) with roof r_V∘θ.
The hypothesis θ_*[r_U] = [r_V] says that r_V∘θ − r_U is a coboundary in C(U,Z). Theorem A gives the conjugacy.
For the flip case, the induced map of (Y,S^{-1}) on V is S_V^{-1} with return time r′_V = r_V∘S_V^{-1}; the classes
[r′_V] and [r_V] agree in K^0(V,S_V), and K^0(Y,S^{-1}) = K^0(Y,S) as groups. Apply the first case to (Y,S^{-1}). ∎

## 2. Corollary B: corner-matrix ring isomorphisms force flip conjugacy
**Corollary B.** Let X and Y be infinite minimal subshifts, U ⊆ X and V ⊆ Y nonempty clopen, and n ≥ 1 with
[1_X] = n[1_U] in K^0(X,T) and [1_Y] = n[1_V] in K^0(Y,S). Suppose φ: e_U R_X e_U → e_V R_Y e_V is a ring isomorphism
with φ(e_U D_X) = e_V D_Y. Then (X,T) and (Y,S) are flip conjugate.

**Proof.**
1. The corner e_U R_X e_U is the Steinberg algebra of the reduction 𝒢_X|_U, with diagonal e_U D_X. For minimal X the
   reduction is the transformation groupoid Z ⋉_{T_U} U: an arrow between two points of U on one T-orbit is a
   unique power of T_U.
2. φ is diagonal-preserving, so `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids` (effective
   groupoids, F_2 indecomposable) gives Z ⋉ U ≅ Z ⋉ V. This induces an isomorphism of topological full groups
   [[T_U]] ≅ [[S_V]], and `topological-full-groups-determine-flip-conjugacy` gives a homeomorphism θ: U → V with
   θ∘T_U = S_V^{±1}∘θ.
3. ι_U[1_X] = [r_U] = n[1_U] and ι_V[1_Y] = [r_V] = n[1_V], and θ_*[1_U] = [1_V]. So θ_*ι_U[1_X] = ι_V[1_Y].
4. Corollary A′ finishes. ∎

**What it kills.**
- A decomposition 1 = Σ_{i<n} f_i of R_X into orthogonal idempotents each equivalent to e_U gives
  R_X ≅ M_n(e_U R_X e_U), and [1_X] = n[1_U] in K_0(R_X) = K^0(X,T) (`subshift-crossed-product-k0-is-coinvariant-group`).
- So every ring isomorphism R_X ≅ R_Y assembled as M_n(φ) from a diagonal-preserving corner isomorphism relates only
  flip conjugate subshifts. This covers the tower identity R_{X^(k)} ≅ M_k(R_X) and every Kakutani-equivalence
  construction.
- Route (a) therefore needs a ring isomorphism whose restriction to EVERY clopen corner fails to be spatial.

## 3. Lemma C: recognition of Z-action groupoids
**Lemma C.** Let G be an ample Hausdorff groupoid with compact unit space, and c: G → Z a continuous homomorphism
such that for every x ∈ G^(0) the restriction c|_{G_x}: G_x → Z is a bijection (G_x = s^{-1}(x)). Then
B_1 = c^{-1}(1) is a full compact open bisection, T = r∘(s|_{B_1})^{-1} is a homeomorphism of G^(0), and
γ ↦ (c(γ), s(γ)) is an isomorphism of topological groupoids G → Z ⋉_T G^(0).

**Proof.**
- B_n = c^{-1}(n) is clopen, since c is continuous and Z is discrete.
- s|_{B_n} is a bijection onto G^(0), by the fibre hypothesis. It is continuous and open, since G is étale and B_n is
  open, so it is a homeomorphism B_n → G^(0). B_n is compact.
- r|_{B_1} is injective: if γ, γ′ ∈ B_1 have r(γ) = r(γ′), then δ = γ^{-1}γ′ lies in G_{s(γ′)} with c(δ) = 0 = c(1_{s(γ′)}),
  so δ is a unit and γ = γ′.
- r|_{B_1} is onto: for y ∈ G^(0), the unique η ∈ G_y with c(η) = −1 has η^{-1} ∈ B_1 and r(η^{-1}) = y.
- So B_1 is a full bisection, and T = r∘(s|_{B_1})^{-1} is a homeomorphism.
- By induction on |n|, the unique arrow in G_x with c = n is the product of n arrows of B_1^{±1}, so its range is T^n x.
- So Φ(γ) = (c(γ), s(γ)) satisfies r(γ) = T^{c(γ)} s(γ), is multiplicative, and is bijective by the fibre hypothesis.
  It is continuous, and its inverse (n,x) ↦ (s|_{B_n})^{-1}(x) is continuous. ∎

Credit: folklore. Note: the brief phrased route (b) through a cocycle with principal AF kernel; Lemma C is the exact
recognition statement (the kernel is then the unit space).

## 4. Theorem D: Cartan uniqueness splits into a cocycle statement and ring rigidity
**Theorem D.** For an infinite minimal subshift X, the following are equivalent.
- (U) Every algebraic Cartan subalgebra of R_X is β(D_X) for a ring automorphism β of R_X.
- (D1) and (D2) together:
  - (D1) for every algebraic Cartan subalgebra B ⊆ R_X, the groupoid model G_B of
    `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` carries a continuous homomorphism G_B → Z that is
    bijective on every source fibre;
  - (D2) every infinite minimal subshift Y with R_Y ≅ R_X as rings is flip conjugate to X.

**Proof.**
- (U) ⇒ (D1): Theorem C(3) of the cited node gives G_B ≅ 𝒢_X, and 𝒢_X carries c(n,x) = n.
- (U) ⇒ (D2): Theorem C(4).
- (D1)+(D2) ⇒ (U). By Theorem C(3) it suffices that every effective ample Hausdorff G with A_{F_2}(G) ≅ R_X is
  isomorphic to 𝒢_X. Such a G is a model G_B for B the image of D(G) (proof of C(3)), so it is minimal with Cantor unit
  space (C(2)).
  - (D1) and Lemma C give G ≅ Z ⋉_T Y with Y = G^(0) a Cantor set and T a minimal homeomorphism. T has no periodic
    points, because Y is infinite and T is minimal.
  - A_{F_2}(Z ⋉_T Y) = LC(Y,F_2) ⋊_T Z ≅ R_X is finitely generated, so (Y,T) is conjugate to a subshift, by
    `crossed-product-el-kazhdan-iff-finite-field-and-subshift`.
  - (D2) gives a flip conjugacy between (Y,T) and (X,T_X). It induces Z ⋉_T Y ≅ 𝒢_X (sending n to −n in the flip case).
    ∎

**Reading.** (D2) is the ring rigidity question among subshifts, and (D1) is an orientation statement about models:
- a model with a torsion isotropy group, or with two-ended orbits that admit no continuous orientation, fails (D1);
- Cartan uniqueness at X holds iff no Cartan model of R_X has such a defect AND R_X determines X among subshifts up to
  flip.

## 5. A test object for (D1): the dihedral Sturmian groupoid
- Let X_α be a Sturmian subshift (irrational α), R the reversal (Rx)_n = x_{−n}. The language is closed under reversal,
  so R preserves X_α and R T R = T^{−1}.
- On X′ = X_α × Z/2 put T′(x,e) = (Tx, e+1) and s(x,e) = (Rx, e+1). Then s² = 1 and s T′ s = T′^{-1}, so
  D_∞ = ⟨T′, s⟩ acts.
- T′ is minimal, because X_α has no eigenvalue −1 (its spectrum is {e^{2πi(kα+m)}}), so D_∞ acts minimally.
- s T′^k fixes (x,e) iff k is odd and x is a bi-infinite palindrome centred at k/2. Such points exist
  (Droubay–Pirillo: Sturmian languages contain palindromes of every even length) and form a nowhere dense set. So the
  action is topologically free but not free.
- G_D = D_∞ ⋉ X′ is effective, minimal, ample, Hausdorff, with Cantor unit space and nontrivial finite isotropy Z/2.
- A groupoid satisfying the hypothesis of Lemma C is a Z-action groupoid, whose isotropy groups are subgroups of Z. So
  G_D carries no fibre-bijective cocycle, and it is not a Z-action groupoid.
- **Open decider.** Is A_{F_2}(G_D) = LC(X′,F_2) ⋊ D_∞ isomorphic as a ring to R_Y for some infinite minimal subshift Y?
  - A yes makes the image of D(G_D) a Cartan subalgebra of R_Y whose model fails (D1), so Cartan uniqueness fails at Y.
  - A no needs a ring invariant separating the two. Candidates: the K_1-index homomorphism of R_Y onto Z
    (`binary-subshift-ring-k1-is-half-orbit-index`), which uses an orientation; the V-monoid.
  - Known agreements: both rings are simple (effective minimal groupoids), finitely generated, and of GK-dimension 2
    (linear complexity).

## 6. Screening for route (a), and dead ends
- **Sturmian subshifts: no candidates.** Their unital ordered K^0 is Z + αZ ⊂ R, which determines α up to α ↦ 1 − α,
  and X_{1−α} is X_α with the two letters exchanged. So strong orbit equivalence among them is flip conjugacy.
- **Corners, amplifications, towers: dead** (Corollary B).
- **Candidate families still standing:** non-flip-conjugate proper orderings on one stationary Bratteli diagram
  (Herman–Putnam–Skau), such as substitutions with equal incidence matrix and equal dimension group. They share the SOE
  class and the linear complexity growth; by Corollary B any ring isomorphism between their crossed products would be
  non-spatial on every corner.

## 7. Sharpest next targets
1. Decide whether A_{F_2}(G_D) ≅ R_Y for some subshift Y (§5). A yes refutes Cartan uniqueness; a no produces a ring
   invariant that sees orientation, the natural first step toward (D1).
2. Prove (D1) through K_1: an algebraic Cartan B of R_X gives [[G_B]] ⊆ GL_1(R_X) as normaliser units (B^× = 1 over
   F_2). If the K_1 index restricted to [[G_B]] comes from a continuous cocycle on G_B, fibre-bijectivity may follow
   from minimality and the growth bound of `subshift-ring-isomorphism-preserves-soe-class-and-growth`.
