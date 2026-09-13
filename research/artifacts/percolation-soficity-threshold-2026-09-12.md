# A soficity threshold for percolation clusters, between p_c and p_u

Lane `ex-free-bridges`, 2026-09-12. Handwritten proofs, no computation. The percolation inputs are imported
claims already on main. The operator-algebraic lemmas are proved here from the definition.

**Summary.**
- Fix a finitely generated group `G` with a finite symmetric generating set `S`. Couple Bernoulli bond
  percolation at every parameter on one probability space. Each parameter `p` gives a cluster subrelation
  `R_p` of the orbit relation of a free Bernoulli shift of `G`.
- In the uniqueness phase `p > p_u`, `R_p` restricted to the infinite cluster *is* the orbit relation
  restricted to a set of positive measure. So it inherits nonsoficity (and non-hyperlinearity) from `G`.
- Below `p_c` every class is finite, hence sofic, and soficity is monotone in `p`.
- So every nonsofic group has a soficity threshold `p_sof(G,S)` with `p_c <= p_sof <= p_u`.
- **Bridge.** For a nonsofic group, one sofic supercritical cluster relation gives `p_c < p_u`: the
  Benjamini--Schramm conjecture for that Cayley graph. Equivalently, a nonsofic counterexample to
  Benjamini--Schramm would make nonsoficity appear exactly at criticality.

## 0. Setting and inputs

`G` is countably infinite, `S` finite symmetric, `1 notin S`, `<S> = G`. `E` is the edge set
`{ {g, gs} : g in G, s in S }` of `Cay(G,S)`, with `G` acting by left multiplication.

- `Omega = [0,1]^E` with product Lebesgue measure `mu`, and `(g.xi)(e) = xi(g^-1 e)`.
- `omega_p(xi)(e) = 1{xi(e) <= p}` is Bernoulli bond percolation at `p`, for all `p` at once.
- `C_p(xi)` is the set of vertices joined to `1` by an `omega_p(xi)`-open path.
- `A_p = { xi : |C_p(xi)| = infinity }`, so `mu(A_p) = theta(p)`.
- `p_c = sup{ p : theta(p) = 0 }`. `p_u` is the uniqueness threshold.

Imported (claims on main):
- (I1) `fpbs-cluster-count-trichotomy`: for `p > p_u` there is a.s. exactly one infinite cluster
  (Newman--Schulman; Häggström--Peres, Schonmann).
- (I2) `fpbs-critical-no-infinite-cluster`: if `Cay(G,S)` is nonamenable, `theta(p_c) = 0` (BLPS).
  It is used only to put `p_c` itself in the sofic set.

**Freeness and ergodicity.** Let `g != 1`. Since `|S| >= 2` for infinite `G`, some edge `e` has `g e != e`:
an edge `{h, hs}` is fixed by `g` only if `gh = hs`, and at most one label at each vertex can satisfy
that. With a nonatomic base, `mu{xi(e) = xi(g^-1 e)} = 0`, so the action is essentially free. Every
edge stabilizer has order at most two, so all `G`-orbits on `E` are infinite. A Bernoulli shift over a
`G`-set with infinite orbits is mixing, hence ergodic.

**The relations.** `R_G = { (xi, g.xi) }` is the orbit relation. Define

    R_p = { (xi, g^-1 . xi) : g in C_p(xi) }.

The cluster of `1` in `g^-1 . xi` is `g^-1 C_p(xi)`, so `R_p` is a Borel equivalence relation. Its classes
are the clusters. It is contained in `R_G`, it preserves `mu`, and `A_p` is `R_p`-invariant. For
`p <= p'` we have `C_p(xi) ⊆ C_(p')(xi)`, so `R_p ⊆ R_(p')`. Also `R_1 = R_G`.

## 1. Soficity of equivalence relations

For a p.m.p. countable Borel equivalence relation `R` on `(X, mu)`, `L(R)` is its von Neumann algebra
with trace `tau`, `L^inf(X) ⊆ L(R)`, and `u_phi` is the unitary of `phi in [R]`.
- Recall `tau(u_phi) = mu{x : phi(x) = x}`.
- `M_omega = prod_omega M_(n_k)(C)` is a tracial ultraproduct, `D_omega` its diagonal part and
  `P_omega` the ultraproduct of the permutation matrices.

**Definition.** `R` is *sofic* if there is a trace-preserving *-embedding `Theta: L(R) -> M_omega` with
`Theta(L^inf X) ⊆ D_omega` and `Theta(u_phi) in P_omega` for all `phi in [R]`. It is *hyperlinear* if
`L(R)` has a trace-preserving embedding into `R^omega`.
- This is the relation analogue of Păunescu's Definition 1.4 for actions (arXiv:1002.0605), as imported in
  `kun-thom-free-nonsofic-action`.
- Every lemma below is proved from this definition. No comparison with combinatorial definitions is used.

**Lemma 1.1 (subrelations).** If `R' ⊆ R` on the same space and `R` is sofic (hyperlinear), so is `R'`.

*Proof.* `L(R') ⊆ L(R)` is a trace-preserving inclusion containing `L^inf(X)`, and `[R'] ⊆ [R]`.
Restrict `Theta`. QED

**Lemma 1.2 (restriction).** If `R` is sofic (hyperlinear) and `mu(A) = a > 0`, then `R|_A` is sofic
(hyperlinear).

*Proof.*
- `L(R|_A) = 1_A L(R) 1_A` with trace `tau / a`. Put `P = Theta(1_A) in D_omega`. Lift it to diagonal
  projections `P_k` of rank `r_k` with `r_k / n_k -> a`. Then `P M_omega P = prod_omega P_k M_(n_k) P_k`,
  with the rescaled trace.
- Let `phi in [R|_A]`, and put `phi^ = phi ⊔ id_(X \ A) in [R]`. Then `Theta(u_(phi^)) = (sigma_k)` is a
  permutation that commutes with `P` in the ultraproduct.
  - So `sigma_k` maps all but `o(n_k)` points of `supp P_k` into `supp P_k`.
  - Changing `sigma_k` on `o(n_k)` points gives a permutation preserving `supp P_k`, with the same
    ultraproduct class.
- Hence `Theta(u_phi) = P Theta(u_(phi^)) P` is a permutation of the corner. Restricting `Theta` to the
  corner gives the required embedding. The hyperlinear case is the corner of an `R^omega` embedding. QED

**Lemma 1.3 (amplification).** Let `R` be ergodic and `mu(A) > 0`. If `R|_A` is sofic (hyperlinear), so
is `R`.

*Proof.*
- **Matrix picture.** By ergodicity there are `psi_1, ..., psi_m in [[R]]` with domains inside `A` whose
  ranges `B_i` partition `X`. Put `v_i = u_(psi_i)`. Then `v_i^* v_i = 1_(dom psi_i) <= 1_A` and
  `sum v_i v_i^* = 1`.
  - `x -> (v_i^* x v_j)_(ij)` is a trace-scaling *-isomorphism of `L(R)` onto the corner
    `p M_m(1_A L(R) 1_A) p`, with `p = diag(v_i^* v_i)`.
  - It sends `L^inf(X)` to diagonal matrices over `L^inf(A)`.
  - For `phi in [R]`, the entries `v_i^* u_phi v_j` are unitaries of partial isomorphisms in `[[R|_A]]`,
    arranged as a partial permutation matrix.
- **Extension to partial isomorphisms.** `R|_A` is ergodic. A partial isomorphism `psi in [[R|_A]]`
  extends to some `psi^ in [R|_A]`, and `u_psi = 1_(ran psi) u_(psi^)`. So `Theta_A(u_psi)` is a
  diagonal projection times a permutation: a partial permutation in the ultraproduct.
- **Assembly.** `M_m(Theta_A)` lands in `prod_omega M_(m r_k)`. It sends the diagonal to the diagonal,
  and each matrix `(v_i^* u_phi v_j)` to a block matrix of partial permutations.
  - These blocks have orthogonal row supports and orthogonal column supports, summing to `p`.
  - So in the ultraproduct the image is a permutation of the support of `M_m(Theta_A)(p)`.
  - Representatives can be corrected on `o(m r_k)` points to be exact permutations.
- Compressing to that support and rescaling the trace gives `Theta` for `R`. The hyperlinear case is
  `M_m(R^omega)` compressed, which embeds in `R^omega`. QED

**Lemma 1.4 (free actions).** If `G` acts essentially freely and `R_G` is sofic (hyperlinear), then `G` is
sofic (hyperlinear).

*Proof.* `g -> Theta(u_g)` is a homomorphism into `P_omega`, the Hamming ultraproduct of symmetric groups.
Its normalized fixed-point proportion is `tau(u_g) = mu(Fix g) = 0` for `g != 1`. So it is an injective
sofic representation. In the hyperlinear case, `u_g` generate a trace-preserving copy of `L(G)` inside
`L(R_G)`. QED

**Lemma 1.5 (finite classes).** A p.m.p. relation all of whose classes are finite is sofic and hyperlinear.

*Proof.*
- **Structure.** Partition `X` by class size into invariant pieces `X_n`. Choose Borel transversals `T_n`
  and Borel enumerations of classes. Then `R|_(X_n) ≅ T_n x {complete relation on n points}`, so
  `L(R|_(X_n)) = L^inf(T_n) ⊗ M_n`, with `L^inf(X_n) = L^inf(T_n) ⊗ D_n`.
- **Full group.** A full group element acts by a measurable `f: T_n -> S_n`, that is
  `sum_pi 1_(f^-1 pi) ⊗ pi`.
- **Embedding.** Embed `L^inf(T_n)` trace-preservingly in `prod_omega D_(m_k)` by finite partitions. Then
  `f` maps to a sum of permutation matrices weighted by complementary diagonal projections, which is a
  permutation matrix.
- Countable direct sums are handled by truncating to finitely many `n` along the ultrafilter. QED

## 2. The uniqueness phase inherits nonsoficity

**Theorem 2.1.** Let `p in (p_u, 1]`. Then `R_p|_(A_p) = R_G|_(A_p)` almost everywhere. If `G` is not sofic
(not hyperlinear), then `R_p` is not sofic (not hyperlinear).

*Proof.*
- **Equality.** Let `(xi, g^-1 . xi) in R_G` with both points in `A_p`. Then `1 in C_infinity(xi)` and
  `g in C_infinity(xi)`. By (I1) there is a.s. one infinite cluster, so `g in C_p(xi)`, and the pair lies
  in `R_p`. The other inclusion holds because `R_p ⊆ R_G`. For `p = 1` every edge is open and
  `R_1 = R_G`.
- **Positive measure.** `mu(A_p) = theta(p) > 0`, because `p > p_u >= p_c`.
- **Nonsoficity.** Suppose `R_p` were sofic. Then:
  - `R_p|_(A_p)` is sofic, by Lemma 1.2;
  - so `R_G|_(A_p)` is sofic;
  - so `R_G` is sofic, by Lemma 1.3, since `R_G` is ergodic;
  - so `G` is sofic, by Lemma 1.4.

  The hyperlinear case is identical. QED

## 3. The threshold

**Theorem 3.1.** Let `Sof(G,S) = { p in [0,1] : R_p is sofic }`.
1. `Sof(G,S)` is a down-set.
2. It contains `[0, p_c)`, and it contains `p_c` when `Cay(G,S)` is nonamenable.
3. If `G` is not sofic, it misses `(p_u, 1]`.

Hence for nonsofic `G`, `p_sof(G,S) := sup Sof(G,S)` satisfies

    p_c <= p_sof(G,S) <= p_u,

`R_p` is sofic for `p < p_sof`, and `R_p` is nonsofic for `p > p_sof`. The same holds for hyperlinearity,
giving `p_c <= p_hyp <= p_u` for every non-hyperlinear group.

*Proof.*
1. If `p' <= p` then `R_(p') ⊆ R_p`, so this is Lemma 1.1.
2. For `p < p_c`, and for `p = p_c` under (I2), `theta(p) = 0`. So every class of `R_p` is finite a.s.,
   and Lemma 1.5 applies.
3. This is Theorem 2.1. QED

**Corollary 3.2 (Benjamini--Schramm from one sofic supercritical cluster).** Let `G` be nonsofic. If `R_p`
is sofic for some `p > p_c`, then `p_c < p_u` on `Cay(G,S)`.

*Proof.* By 3.1(3), `p <= p_u`, so `p_c < p <= p_u`. QED

**Contrapositive.** If a nonsofic group had `p_c = p_u` on some Cayley graph, every supercritical cluster
relation would be nonsofic. Nonsoficity would then switch on exactly at criticality.

## 4. Remarks and scope

- **What is new, what is folklore.** The equality `R_p|_(A_p) = R_G|_(A_p)` in the uniqueness phase is
  standard in the orbit-equivalence treatment of percolation. Lemmas 1.1--1.5 are standard permanence
  properties of sofic relations. The new content is the threshold `p_sof` for nonsofic groups, which exist
  only since 2026-08 (`openai-leavitt-unit-nonsofic`), and the reduction in Corollary 3.2.
- **Where it applies.** It applies to the binary Leavitt unit group `U`, for every finite generating set.
  `U` has fixed price one (`leavitt-unit-groups-have-fixed-price-one`), so the cost route
  `fpbs-non-fixed-price-one-has-nonuniqueness` gives nothing for `U`. Its first `L^2`-Betti number is `0`,
  so the Betti-number route gives nothing either. Corollary 3.2 is a tool of a different kind.
- **The decoration matters.** `R_p` lives on the full configuration space. The rooted labeled cluster
  alone is a factor, and a factor of a nonsofic relation can be sofic.
  - *Sketch, not claimed.* Finite models of the labeled cluster network, with missing edges filled in
    arbitrarily, satisfy the words of a nonsoficity certificate `(F, eps_0)` of word length `L` wherever the
    word paths are open. By FKG that happens with conditional probability at least `p^(3L)`.
  - So the labeled cluster network should be nonsofic once `p^(3L) > 1 - eps_0`. That only reaches `p`
    near `1`, and Theorem 3.1 does not use it.
- **Open.**
  - (Q1) Is `p_sof(G,S) > p_c` for every nonsofic `G`? A yes gives Benjamini--Schramm for every nonsofic
    group.
  - (Q2) Is `p_sof = p_u`?
  - (Q3) Are the cluster relations of the nonuniqueness phase treeable? Treeable relations are sofic, which
    would answer Q1.
  
  Nothing here decides any of them.
