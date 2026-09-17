# Finite contacts across almost malnormal subgroups, and a Linnell-free injectivity lemma

September 17, 2026. Worker `swarm-0917-w2-fp-pull-1`, cone
`fpbs-fixed-price-universal`, target
`fpbs-fixed-price-non-amenably-generated-from-fg`.

Contents:
- §1 proves a counting bound for graphing edges between two classes of a
  subgroup orbit relation (Theorem 1).
- §2 derives the obstruction for the established criterion
  `fpbs-infinite-contact-zero-relative-cost` (Corollary 2) and applies it to
  `Gamma_mal` (Corollary 3).
- §3 proves an elementary injectivity lemma for group-ring elements
  `1 - T` with `T` homogeneous (Lemma 4). It gives a second proof of
  `beta_1^(2)(Gamma_mal) = 1` that uses neither Linnell's theorem nor
  Jaikin-Zapirain's `L²`-independence (Proposition 5).
- §4 records what remains and some side observations.

Script: `experiments/fpbs-locally-free-malnormal-union-2026-09-17/fox_homogeneity.py`
recomputes the Fox matrix used in §3 and exits nonzero if a check fails.

All deductions here are written proofs. They have not been formally verified.

---

## 1. The counting bound

**Setting.**
- `Gamma` is a countable group with a free p.m.p. action `a` on `(X, mu)`, and
  `E_a` is its orbit relation.
- `Lambda <= Gamma` is a subgroup.
- `Phi` is a graphing with `Phi ⊆ E_a` and finite cost `c(Phi)`, given as a
  countable family of partial Borel isomorphisms `phi_j : A_j -> B_j`. Its
  cost is `c(Phi) = sum_j mu(A_j)`.

Because the action is free, each `A_j` splits into Borel pieces
`A_{j,g} = {x in A_j : phi_j(x) = g x}`, one for each `g in Gamma`. Put
`m_g(x) = #{j : x in A_{j,g}}`. Then `sum_g ∫ m_g dmu = c(Phi)`.

**Double cosets.** For `gamma in Gamma` put
`I(gamma) = Lambda ∩ gamma^{-1} Lambda gamma`. Replacing `gamma` by
`mu gamma lambda`, with `mu, lambda in Lambda`, conjugates `I(gamma)` by
`lambda^{-1}` and does not change its cardinality. So the set

    Q(Lambda) = { gamma in Gamma : I(gamma) is infinite }

is a union of double cosets `Lambda gamma Lambda`.

Take a point `y` and a class `C'` of `E_{a|Lambda}` in the orbit of `y`. Then
`C' = Lambda gamma y` for some `gamma`, and the double coset `Lambda gamma
Lambda` depends only on the pair of classes `(Lambda y, C')`. So "the pair is
of type `Q`" is well defined.

**Edge count.** Let `N_gamma(x)` be the number of `Phi`-edges, counted with
multiplicity and in both orientations, joining the classes `Lambda x` and
`Lambda gamma x`.

**Theorem 1.** For every `gamma in Gamma`,

    ∫ N_gamma dmu <= 2 |I(gamma)| c(Phi).

So if `gamma notin Q(Lambda)`, then `N_gamma < infinity` almost everywhere.
There is a `Gamma`-invariant conull set `X_0` with this property: for every
`x in X_0`, every two `E_{a|Lambda}`-classes in the orbit of `x` whose pair is
not of type `Q` are joined by only finitely many `Phi`-edges.

*Proof.*
1. **Outgoing edges.** An edge leaves `Lambda x` at `lambda x` through the
   piece `A_{j,g}` and lands at `g lambda x`. By freeness it lands in
   `Lambda gamma x` exactly when `g lambda in Lambda gamma`. So the count of
   outgoing edges is

       N^+_gamma(x) = sum_g sum_{lambda in Lambda} m_g(lambda x) 1[g lambda in Lambda gamma].

2. **Integrate.** The action preserves `mu`, so

       ∫ N^+_gamma = sum_g ∫ m_g · #{lambda in Lambda : lambda in g^{-1} Lambda gamma}.

3. **Bound the inner count.** The set `Lambda ∩ g^{-1} Lambda gamma` is either
   empty or a left coset of `I(gamma)`. Indeed, if `lambda_0 = g^{-1} mu_0
   gamma` and `lambda = g^{-1} mu gamma` both lie in `Lambda`, then

       lambda_0^{-1} lambda = gamma^{-1} mu_0^{-1} mu gamma in Lambda ∩ gamma^{-1} Lambda gamma.

   So the inner count is at most `|I(gamma)|`, and
   `∫ N^+_gamma <= |I(gamma)| c(Phi)`.
4. **Incoming edges.** These are the outgoing edges from the class of
   `y = gamma x` into `Lambda gamma^{-1} y`. So
   `N^-_gamma(x) = N^+_{gamma^{-1}}(gamma x)`, and its integral is at most
   `|I(gamma^{-1})| c(Phi)`. Also `I(gamma^{-1}) = gamma I(gamma) gamma^{-1}`
   has the same cardinality as `I(gamma)`.
5. **Conull set.** Let `X_0` be the intersection, over `delta in Gamma` and
   `gamma notin Q(Lambda)`, of the conull sets `{x : N_gamma(delta x) <
   infinity}`. This is a countable intersection, and it is `Gamma`-invariant.
   Every pair of classes in the orbit of `x` has the form
   `(Lambda delta x, Lambda gamma delta x)`. ∎

The proof uses only freeness, invariance of `mu`, and the coset count. No
cost theory is imported.

## 2. The obstruction for infinite-contact repair

The established claim `fpbs-infinite-contact-zero-relative-cost` works as
follows.
- **Input.** A simple finite-cost generating graphing `H` of `R = E_a`, and a
  subrelation `S`.
- **Class graph.** In each orbit, connect two `S`-classes when infinitely many
  `H`-edges run between them.
- **Conclusion.** If this graph is connected almost surely, then
  `relC(R; S) = 0`, and `C(R) <= c(F)` for every finite-cost graphing `F` of
  `S`.

**Corollary 2 (where subgroup-orbit contact repair dies).**
- **Setting.** `Gamma` is countably infinite with a free action `a`,
  `Lambda <= Gamma`, and `S` is a subrelation of `E_{a|Lambda}` (for example
  `S = E_{a|Lambda}` itself).
- **Connectivity condition.** For every finite-cost graphing `H` of `E_a`, the
  class graph above is connected almost surely only if
  `<Q(Lambda)> = Gamma`. On the conull set `X_0` of Theorem 1, the component
  of the `S`-class of `x` lies inside `<Q(Lambda)> x`.
- **wq-normality.** `<Q(Lambda)> = Gamma` implies that `Lambda` is wq-normal in
  `Gamma`.
- **Almost malnormal subgroups.** Suppose `Lambda` is contained in a proper
  subgroup `M` with `M ∩ gamma^{-1} M gamma` finite for all `gamma notin M`.
  Then `<Q(Lambda)> ⊆ M`. So the criterion with `S ⊆ E_{a|Lambda}` fails for
  every free action and every finite-cost graphing.

*Proof.*
1. **Contacts between `S`-classes.** Let `C ⊆ Lambda y` and
   `C' ⊆ Lambda gamma y` be `S`-classes with infinite contact. Then the classes
   `Lambda y` and `Lambda gamma y` have infinite contact. By Theorem 1, for
   `y in X_0`, the pair is of type `Q`. So every edge of the class graph either
   stays inside one `Lambda`-class, or moves from `Lambda y` to
   `Lambda gamma y` with `gamma in Q(Lambda)`.
2. **The component.** Following a path, the `S`-classes reachable from the
   class of `x` lie in `Lambda`-classes `Lambda gamma_k ... gamma_1 x` with
   every `gamma_i in Q(Lambda)`. Here each `gamma_i` is taken relative to the
   current base point, which is legitimate because type `Q` depends only on
   the pair.
3. **The group generated.** If `Lambda` is infinite, then `Lambda ⊆ Q(Lambda)`,
   so the component lies in `<Q(Lambda)> x`. If `Lambda` is finite, then
   `Q(Lambda)` is empty and the component lies in `Lambda x`.
4. **Connectivity.** The component is the whole orbit `Gamma x` only if
   `<Q(Lambda)> x = Gamma x`. By freeness this means `<Q(Lambda)> = Gamma`. If
   `Lambda` is finite, it would force `Gamma = Lambda`, which is excluded.
5. **wq-normality.** Let `K` be a proper subgroup with `K ⊇ Lambda`. Some
   `gamma in Q(Lambda)` lies outside `K`. Then

       gamma K gamma^{-1} ∩ K ⊇ gamma Lambda gamma^{-1} ∩ Lambda = gamma I(gamma) gamma^{-1},

   which is infinite. This is the intermediate-subgroup definition of
   wq-normality used in `fpbs-wq-normal-hull-is-almost-malnormal`.
6. **Almost malnormal `M`.** If `gamma notin M`, then
   `I(gamma) ⊆ M ∩ gamma^{-1} M gamma`, which is finite. So
   `Q(Lambda) ⊆ M`. ∎

**The invariant and the step.**
- **Invariant.** The first hull step `W_1(Lambda) = <Q(Lambda)>`, that is, the
  subgroup generated by the elements whose conjugate of `Lambda` meets
  `Lambda` in an infinite set.
- **Step.** Every member of the approach "repair `E_a` from a subgroup orbit
  relation by infinite contacts" dies at the connectivity hypothesis of the
  criterion whenever `W_1(Lambda) != Gamma`. The failure does not depend on
  the action or the graphing.

This is sharper than wq-normality. In the recursion of
`fpbs-wq-normal-hull-is-almost-malnormal`, a wq-normal `Lambda` with
`W_1(Lambda) != Gamma` still fails the criterion in one step. It can be used
only stepwise: first `Lambda` inside `W_1`, then `W_1` inside `W_2`, and so on.
Each step needs its own finite-cost graphing of the intermediate relation with
matching cost.

The corollary shows only that this particular criterion cannot apply. It does
not show that `relC(E_a; E_{a|Lambda}) > 0`. See §4 for the `L²` side, where
no obstruction appears.

**Corollary 3 (`Gamma_mal`).**
- **Setting.** Let `Gamma_mal = union_n H_n` with `H_n ≅ F_2`, built along
  `a -> a`, `b -> b a b^{-2}`. The stages `H_n` are malnormal in `H_{n+1}`, by
  the Stallings-graph certificate in
  `research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md`
  §5.1. Hence they are malnormal in `Gamma_mal`.
- **Conclusion.** Let `Lambda` be a subgroup contained in some stage. This
  covers every finitely generated subgroup and every subrelation of
  `E_{a|H_n}`, including the stepwise pairs `(E_{a|H_{n+1}}, E_{a|H_n})`. For
  such `Lambda`, the infinite-contact criterion with `S ⊆ E_{a|Lambda}` fails
  for every free action of `Gamma_mal` and every finite-cost graphing. A
  repair of this kind must use subrelations not contained in any stage orbit
  relation.

*Proof.* Corollary 2 applies with `M = H_n`, where
`H_n ∩ gamma^{-1} H_n gamma = 1` for every `gamma notin H_n`. ∎

The same argument covers Proposition F anchors of
`research/artifacts/fpbs/docs/fixed-price-countable-passage.md` §5.
- Normal or commensurated infinite anchors `Lambda` have
  `Q(Lambda) = Gamma`. The criterion is not blocked there, and those are
  exactly the anchors Proposition F already handles.
- Contact repair from a subgroup orbit relation adds nothing outside groups
  with an infinite subgroup `Lambda` satisfying `W_1(Lambda) = Gamma`.

**Structural consequence for a finite-cost action of `Gamma_mal`.** Suppose a
free action `b` of `Gamma_mal` has finite cost. Then, for every finite-cost
graphing `Phi` of `E_b`, every `n`, and almost every `x`, only finitely many
`Phi`-edges run between any two distinct `H_n`-classes in the orbit of `x`.
Such a graphing is "locally finite across stages". This is a property any
treeing or finite-cost graphing produced for
`fpbs-locally-free-free-actions-have-finite-cost` must have.

## 3. An elementary injectivity lemma

**Lemma 4.**
- **Setting.** Let `G` be a countable group with a homomorphism
  `ht : G -> Z`. Let `T = sum_i c_i g_i` be a finite sum in `CG` with every
  `g_i` of the same height `m != 0`.
- **Operators on `ℓ²G`.** Left multiplication `lambda(1 - T)` and right
  multiplication `rho(1 - T)` are injective with dense range.
- **Group von Neumann algebra.** For the algebra `N(G) = rho(G)'`, the map
  `u -> u lambda(1 - T)` is injective on `N(G)`.

*Proof.*
1. **Circle action.** For `|z| = 1` let `(U_z v)(w) = z^{ht(w)} v(w)`. This is a
   unitary with `U_z delta_e = delta_e`. A direct computation gives
   `U_z lambda(g) U_z^{-1} = z^{ht(g)} lambda(g)`, so
   `U_z lambda(T) U_z^{-1} = z^m lambda(T)`. Hence `U_z` maps
   `V_1 = ker(lambda(T) - 1)` onto `ker(lambda(T) - z^m)`.
2. **Equal traces.** Each `V_mu = ker(lambda(T) - mu)` is invariant under
   `rho(G)`, because `lambda(T)` commutes with `rho(G)`. So its projection
   `p_mu` lies in `N(G)` and has trace `tau(p_mu) = <p_mu delta_e, delta_e>`.
   Since `p_{z^m} = U_z p_1 U_z^{-1}` and `U_z delta_e = delta_e`, all these
   traces equal `tau(p_1)`.
3. **Independent eigenspaces.** Because `m != 0`, the values `z^m` run over
   the whole circle. Choose `N` distinct values `mu_1, ..., mu_N`.
   - The closure of `V_{mu_1} + ... + V_{mu_{N-1}}` lies in the closed
     subspace `ker prod_{i<N} (lambda(T) - mu_i)`.
   - On `V_{mu_N}` this product acts as the nonzero scalar
     `prod_{i<N} (mu_N - mu_i)`. So the two subspaces meet only in 0.
4. **Kaplansky's formula.** For projections `p`, `q` in a finite von Neumann
   algebra, `tau(p ∨ q) + tau(p ∧ q) = tau(p) + tau(q)`.
   - In the polar decomposition of `(1 - q) p`, the partial isometry has left
     support `p ∨ q - q` and right support `p - p ∧ q`.
   - Apply the formula `N - 1` times with `p ∧ q = 0`. This gives
     `tau(p_{mu_1} ∨ ... ∨ p_{mu_N}) = N tau(p_1) <= 1`.
   - `N` is arbitrary, so `tau(p_1) = 0`. The trace is faithful, so `p_1 = 0`.
     So `lambda(1 - T)` is injective.
5. **Dense range.** The adjoint is `lambda(1 - T*)` with
   `T* = sum_i conj(c_i) g_i^{-1}`, which is homogeneous of degree
   `-m != 0`. By step 4 it is injective, so `lambda(1 - T)` has dense range.
   Using `rho` and the same `U_z` gives the right-multiplication statement.
6. **`N(G)`.** If `u lambda(1 - T) = 0`, then `u` vanishes on a dense subspace,
   so `u = 0`. ∎

**Remark (subgroups).** Let `G <= Gamma` and `x in CG`. Then `ℓ²Gamma` is the
orthogonal sum of the spaces `ℓ²(G g)` over right cosets, and `lambda(x)`
preserves each of them. So injectivity and dense range of `lambda(x)` pass
from `ℓ²G` to `ℓ²Gamma`, and so does the `N(Gamma)` statement. Only a height
function on `G` is needed, not on `Gamma`.

**Proposition 5 (second proof that `beta_1^(2)(Gamma_mal) = 1`).**

*Proof.*
1. **Stage chain complex.** Let `V = N(Gamma_mal)`. The rose of `H_n` gives
   the complex `V^2 -> V`, `(v_1, v_2) -> v_1(a - 1) + v_2(b - 1)`, where `b`
   is the second basis element of `H_n`.
2. **`H_0` vanishes.** `H_0 = V ⊗_{ZH_n} Z` is
   `V ⊗_{N(H_n)} (N(H_n) ⊗_{CH_n} C)`. This is 0 because `F_2` is
   nonamenable (Lück 1998, Lemma 3.4.2). Induction is faithfully flat and
   preserves dimension (Theorem 3.3).
3. **`H_1` has dimension 1.** By additivity (Theorem 0.6.4(c)) applied to
   `0 -> H_1 -> V^2 -> V -> H_0 -> 0`, `dim H_1(H_n; V) = 1`.
4. **Stage maps.** The inclusion `H_n -> H_{n+1}` sends the basis
   `(a, b_n)` to `(a, b a b^{-2})`, where `b = b_{n+1}`. On 1-chains it acts
   by the left Fox matrix, recomputed by the script:

       J = [[1, 0], [b, 1 - b a b^{-1} - b a b^{-2}]].

   With `ht(a) = 1` and `ht(b_{n+1}) = 0` on `H_{n+1}`, the element
   `x = 1 - b a b^{-1} - b a b^{-2}` is `1 - T` with `T` homogeneous of degree
   1. The chain map is `(v_1, v_2) -> (v_1 + v_2 b, v_2 x)`.
5. **Injectivity.** If the image is 0, then `v_2 x = 0`, so `v_2 = 0` by
   Lemma 4 and the Remark, and then `v_1 = 0`. So the maps
   `H_1(H_n; V) -> H_1(H_{n+1}; V)` are injective. The height function differs
   from stage to stage (`ht(b_n)` alternates between 0 and 1). This does no
   harm, because each stage map uses its own `H_{n+1}`.
6. **Colimit.** Take the mapping telescope `Y` of the roses. It is a
   `K(Gamma_mal, 1)`, its universal cover is `E Gamma_mal`, and the preimage
   of `Y_n` is `Gamma_mal ×_{H_n} Ỹ_n`. Singular chains commute with directed
   unions of subcomplexes, so
   `H_1(Gamma_mal; V) = colim_n H_1(H_n; V)`.
7. **Dimension.** Lück 1998, Theorem 2.9.1, gives
   `dim(colim_I M_i) = sup{dim(im(psi_i))}`. The maps are injective, so
   `dim H_1(Gamma_mal; V) = 1`. ∎

Verbatim imports (Lück, "Dimension theory of arbitrary modules over finite
von Neumann algebras and applications to L²-Betti numbers", arXiv
dg-ga/9707011, J. reine angew. Math. 495 (1998)):
- Theorem 2.9.1: "dim (colimI Mi) = sup {dim(im(ψi)) | i ∈ I}".
- Theorem 3.3: "Let i : ∆ → Γ be an injective group homomorphism. Then: 1.
  Induction with i is a faithfully flat functor… 2. For any N(∆)-module M we
  have: dimN(∆)(M) = dimN(Γ)(i∗M)".
- Introduction: "Γ is non-amenable if and only if N(Γ) ⊗CΓ C is trivial
  (Lemma 3.4.2)".
- Theorem 0.6.4(c), Additivity, for exact sequences of `N(Γ)`-modules.

Comparison with the landed result:
- `locally-free-groups-first-l2-betti-equals-c-star-minus-one` (landed by
  `swarm-0917-w2-fp-pull-2`) proves `beta_1 = c* - 1` for all locally free
  groups, using Jaikin-Zapirain's `L²`-independence of compressed subgroups.
- Proposition 5 is an independent check of the case `Gamma_mal`, from
  first principles.
- Lemma 4 also applies to ascending unions of free groups whose stage maps
  have a triangular Fox matrix with diagonal entries `1` or `1 - homogeneous`.
  There, stage injectivity can be certified without any `L²`-independence
  theorem.

## 4. What remains, and side observations

- **Upper bound for `Gamma_mal`.** The dichotomy landed by pull-2 pins every
  finite free cost of `Gamma_mal` at 2 (Tucker-Drob arXiv:1211.6395 Prop
  6.7(1) with Gaboriau's fixed price for free groups). So contact repair is
  not needed to bound finite costs from above. What is missing is finiteness:
  `fpbs-locally-free-free-actions-have-finite-cost`. The graphing that a
  finite-cost action would need must be locally finite across stages (§2).
- **Where the contact route could still help.** For the target class beyond
  locally free groups, Corollary 2 confines the contact route to subgroups
  with `W_1(Lambda) = Gamma`. That is the commensurated-type regime already
  covered by Proposition F.
- **No `L²` obstruction to `relC(E_{H_{n+1}}; E_{H_n}) = 0`.** In the relative
  `ℓ²` cokernel bound, the relative first `L²`-Betti number of the stage pair
  is 0, because the stage maps are injective with equal dimensions. So
  Corollary 3 blocks the criterion, not the value of the relative cost.
- **Edges from `b`-repairs only.** Suppose the repairs use only the partial
  maps `b|A`. Then each pair of `K`-cosets, with `K = <a, b a b^{-2}> = H_n`
  inside `H_{n+1}`, carries at most one `b`-edge.
- **A bootstrap rule.** The coset complex of `H_n` in `H_{n+1}` has triangles
  from the relation `c b^2 = b a`, where `c = b a b^{-2}`. So a repair that
  joins two of the three cosets `x`, `a x`, `b x` also joins the third.
- **Trichotomy for `Gamma_mal`.** Exactly one holds:
  - all free costs are 2, so fixed price is 2;
  - costs are mixed, so `Gamma_mal` is an unconditional counterexample to
    fixed price;
  - all free costs are infinite, so the fixed price is ∞.

  The last two each answer Tucker-Drob Q 7.6 positively.
