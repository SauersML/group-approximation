# Positive-side verification (lane gk-vf-positive)

Lane `gk-vf-positive`, 2026-09-12, verifier for the positive family (`gk-p-*`) and the
free lanes by topic. Every verdict here is an independent re-derivation on paper, not
a rereading of the author's argument. No computation.

## 1. Positive anchors no verifier had covered (main at `75257fdaba`)

Neither `gk-verify-pos`'s artifact nor any earlier verdict mentions these ids.

### 1.1 `end-fixing-tree-symmetries-carry-strict-automata` (gk-rokhlin, landing gk-free's calibration). Verdict: PASS.

Re-derivation.

* **Setting.** `T` is the 3-regular tree, `xi` an end, `p(v)` the neighbour toward
  `xi`, and `Gamma = Aut(T, xi)`.
  * Every `gamma` fixing `xi` maps the ray from `v` to `xi` onto the ray from
    `gamma v` to `xi`. So `gamma p = p gamma`, and `gamma` maps the children of `w`
    onto the children of `gamma w`.
  * `Gamma` is transitive on vertices: hyperbolic automorphisms along lines through
    `xi` move the Busemann level, and elliptic ones fixing a ray act transitively on
    each horosphere.
* **Amenable.** The Busemann character `beta: Gamma -> Z` has kernel the horocyclic
  subgroup. That kernel is the increasing union of the compact open stabilizers of
  the vertices along a ray to `xi`, so it is amenable, and `Gamma` is an extension of
  `Z` by it. This is amenability as a locally compact group, which is all the claim
  asserts.
* **Not unimodular.** Taking vertex stabilizers, the modular function is
  `Delta(gamma) = 2^{±beta(gamma)}`, nontrivial on hyperbolic elements.
* **Strict automaton.**
  * `tau(x)(v) = x(p(v))` is equivariant, reads one site, and is continuous.
  * `sigma(y)(w) = min(y(c), y(c'))` reads the unordered pair of children, so it is
    equivariant for a totally ordered alphabet.
  * On `tau(x)` both children of `w` carry `x(w)`, so `sigma tau = id`, and `tau` is
    injective.
  * A configuration giving two siblings different symbols is not in the image.
  So `tau` is strict.
* **Calibration scope.** The index set is a homogeneous space of a nondiscrete group,
  not the group itself. Over a group acting on itself, the equivariant self-maps of
  the index set are the right multiplications, and they are bijections, so the copying
  mechanism does not exist there. The claim says exactly this and nothing stronger.

### 1.2 `injective-measure-preserving-ca-is-surjective` (gk-other-hosts). Verdict: PASS.

`Y = tau(A^G)` is compact, hence closed. From `tau_* mu_A = mu_A`,
`mu_A(Y) = mu_A(tau^-1 Y) = 1`. The open complement is `mu_A`-null, and the uniform
Bernoulli measure gives every nonempty cylinder positive mass, so the complement is
empty. The converse direction in the artifact also holds: a proper closed image has
open nonempty complement, of positive mass, so `mu_A(Y) < 1 = tau_* mu_A(Y)`.
Injectivity plays no role, as the route body correctly remarks.

### 1.3 `every-injective-ca-preserves-uniform-bernoulli-measure` and its three routes. Verdict: PASS.

* **Window balance.** With encoder memory `M`,
  `tau_* mu_A(C_p) = |A|^-|Omega M| · #{q in A^(Omega M) : tau(q)|_Omega = p}`.
  Two probability measures that agree on all cylinders are equal. So preservation is
  exactly the count `|A|^(|Omega M| - |Omega|)` for every finite `Omega` and every
  `p`, as stated.
* **`gottschalk-via-universal-bernoulli-preservation`.** Valid: 1.2 applied
  automaton by automaton.
* **`bernoulli-preservation-from-gottschalk`.** Valid. Surjunctivity makes each
  injective automaton bijective. `bijective-ca-preserve-uniform-bernoulli-measure`
  already passed in Section 20 of `gk-verify-pos-permanence-chain-2026-09-12.md`. I
  re-derived it independently:
  * for a local permutation `pi` on a finite `F`, `rho = sigma pi tau` changes only
    the coordinates in `F M_sigma^-1`;
  * for each boundary condition, `rho` permutes `A^(F M_sigma^-1)`, so it preserves
    `mu_A`;
  * then `pi_* tau_* mu_A = tau_* rho_* mu_A = tau_* mu_A`, and invariance under all
    local permutations characterizes `mu_A`.
* **`universal-bernoulli-preservation-covers-leavitt-units`.** Valid, by
  specialization.
* **Not premature.** The goal cycle is intended and cannot fire: its open prerequisite
  is equivalent to the goal.

### 1.4 `injective-cas-over-leavitt-units-preserve-uniform-bernoulli` (open). Verdict: statement and Attempts correct; wiring incomplete, repaired.

The claim is equivalent to `leavitt-unit-group-surjunctive`, not merely sufficient for
it. The converse holds: if `U` is surjunctive, every injective automaton over `U` is
bijective and so preserves `mu_A` (1.3). The graph recorded only the forward direction
(`leavitt-units-surjunctive-via-measure-preservation`) and the specialization from
the universal claim. The converse route
`leavitt-bernoulli-preservation-from-surjunctivity` is landed with this artifact, so
the equivalence is explicit and a later lane cannot mistake the measure claim for a
weaker, easier target.

I also checked the coset-shift witness cited in the Attempts
(`compressed-coset-shifts-carry-strict-equivariant-embeddings`).
* `psi(gV_1) = g u^-1 V_1` is well defined because `u V_1 u^-1 <= V_1`.
* It is equivariant and surjective.
* It is non-injective exactly when the inclusion is strict: equal images mean
  `g^-1 g'` lies in `u^-1 V_1 u`, which strictly contains `V_1`.

So `y -> y o psi` is injective and not surjective on `A^(U/V_1)`. It is a calibration
on a non-free coset shift, not an automaton over `U`, which is exactly how the node
uses it.

### 1.5 `finitely-generated-simple-groups-are-surjunctive` and `gottschalk-via-finitely-generated-simple-groups` (gk-other-hosts). Verdict: PASS.

* **Localization.** The rule reads only `gM`, which lies in `gH` for `H = <M>`. So
  `A^G` is the product over left cosets of copies of `A^H`, and `tau` acts factor by
  factor. Injectivity and surjectivity then pass in both directions between `tau` and
  `tau_H`.
* **Embedding.** `countable-group-embeds-in-two-generator-simple-group` (Schupp 1976)
  is a citation node with its own transcription caveat. It is a trust surface, not
  re-read here.
* **Heredity direction.** Surjunctivity passes from the simple overgroup `S` down to
  `H`, which is the direction used.

### 1.6 Direct-attack artifact, Sections 2–3 (gk-other-hosts). Verdict: correct as scoped.

Section 2 is 1.2 plus its converse. Section 3 is explicitly heuristic prose ("do not,
on their own, prove surjunctivity"), and it asserts no theorem that a node consumes.
Nothing in it is premature.

## 2. Conjugacy invariants and partition-bounded invariants (gk-p-bernoulli-ergodic, `b14384765f`)

Artifact `research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md`.

### 2.1 `measure-conjugacy-invariants-cannot-certify-surjectivity`. Verdict: PASS, with one scope correction.

* **Theorem 1(a).** `tau` is continuous, injective and equivariant on the compact
  Hausdorff space `A^G`, so it is a homeomorphism onto the closed subshift `Y`. That
  is a topological conjugacy `A^G -> Y`.
* **Theorem 1(b).** `nu = tau_* mu` is `G`-invariant because `tau` is equivariant, and
  `nu(Y) = 1`. `tau` is a Borel equivariant bijection `A^G -> Y` carrying `mu` to `nu`.
  So it is an isomorphism of measure-preserving actions, mod the `nu`-null set
  `A^G \ Y`.
* **The decoder.** A CA decoder `sigma` exists: `tau^-1` is uniformly continuous on
  `Y`, so `tau^-1(y)(1)` depends on a finite window of `y`, and the local rule can be
  extended arbitrarily to patterns not occurring in `Y`.
* **Corollary 1.1, item by item.** Every entry is a genuine isomorphism invariant.
  * **Koopman representation.** Its unitary class on `L^2_0` is transported by the
    isomorphism. That covers ergodicity, weak mixing, mixing, mixing of all orders,
    strong ergodicity and spectral gap.
  * **Weak equivalence class.** Isomorphic actions weakly contain each other.
  * **Orbit relation.** An isomorphism is an orbit equivalence, so cost and `l^2`-Betti
    numbers agree.
  * **Crossed product.** The pair `(L^inf(X) ⋊ G, L^inf(X))` is transported. Scope:
    "Cartan subalgebra" presupposes essential freeness, which the Bernoulli action has
    exactly when `G` is infinite. Finite `G` is surjunctive anyway.
  * **Cocycle superrigidity.** Cocycles and their cohomology classes are transported.
  * **Entropies.** Rokhlin entropy, sofic entropy for a fixed sofic approximation
    (Kerr–Li define it without generators, invariantly), naive entropy (a sup-inf over
    all finite partitions) and the f-invariant (Bowen proved it independent of the
    finite-entropy generating partition) are all invariants.
* **Scope correction to Corollary 1.2 and to the claim sentence** "a property of
  invariant measures that holds for `mu` and fails for every strict image must depend
  on the coordinate structure". Read literally this is false whenever `G` carries no
  strict automaton on `A`: the hypothesis is then vacuous, and ergodicity satisfies it
  over any amenable infinite `G`.
  * *What does hold:* for every isomorphism-invariant property `S` and every strict
    `tau`, `S(tau_* mu) = S(mu)`.
  * *Consequence:* for invariant `S` with `S(mu)`, the separation hypothesis "`S` fails
    at every strict image" is equivalent to "no strict automaton exists on `A^G`". The
    separation step of such an argument is the conclusion restated, never its mechanism.
  This is the conclusion the lane wants, and nothing downstream uses the literal form.
  Correction paragraphs are appended to the claim, its route and the author's artifact.

### 2.2 `rokhlin-entropy-is-the-largest-partition-bounded-invariant`. Verdict: PASS.

* **(a)** `h^Rok <= H(Q)` for generating `Q` by definition. It is an invariant because
  an isomorphism carries generating partitions to generating partitions and preserves
  Shannon entropy.
* **(b)** Take the infimum over generating `Q`.
* **(c)** `log|A| = I <= h^Rok <= H_mu(P) = log|A|`, with the time-zero partition `P`
  generating.
* **Seward scope.** `h^Rok` is defined for ergodic actions. The Bernoulli action is
  ergodic, and free, exactly when `G` is infinite, so (c) applies for infinite `G`.
  No freeness is needed for (a) or (b).
* **Values.** Sofic entropy can be `-infinity`, and the f-invariant can be negative. So
  the examples need invariants valued in `[-infinity, infinity]`, not `[0, infinity]`.
  (b) and (c) are unchanged.
* **f-invariant remark.** `F(Q) <= H(Q)` alone bounds `F`, not `f`. The remark also
  needs Bowen's monotonicity `F(Q^{B_(n+1)}) <= F(Q^{B_n})`, which gives
  `f = inf_n F(Q^{B_n}) <= F(Q) <= H(Q)`. Nothing consumes the examples.
* **Corollary 2.1.** Correct. A lower bound `I((A^k)^G) >= k log|A|` for a
  partition-bounded `I` implies, by (c), Bernoulli Rokhlin maximality at `k`.
  * The deficit step is `strict-automaton-lowers-bernoulli-rokhlin-entropy`, where
    `k(log q - delta/D) + log 3 < k log q` for large `k`.
  * So INF is a consequence of the lower-bound step of every such architecture. This
    is an honest classification, not a restatement dressed as a reduction.

## 3. Simple Kazhdan groups have no proper co-amenable subgroups (gk-p-inf-f, `20cb4ff68`)

Artifact `research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md`.

### 3.1 `simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`. Verdict: PASS.

* **Finite index.** A `G`-invariant mean on `G/H` gives almost invariant unit vectors in
  `l^2(G/H)` (Day, then square roots). Property (T) upgrades them to a nonzero invariant
  vector, which is constant, so `G/H` is finite. This is `no-invariant-mean-on-coset-space`,
  which has its own proof route.
* **Simplicity.** The kernel of `G -> Sym(G/H)` is normal of finite index. It is not
  trivial, because `G` is infinite, so by simplicity it is `G`. Every `g` fixes the coset
  `H`, so `H = G`.
* **What is not consumed.** The instance line "(T) through `R^x = EL_12(R)`" feeds no
  node.

### 3.2 Mechanism analyses (Sections 1.2, 2.3, 3, 4). Verdict: correct as scoped.

Each section is labelled a mechanism analysis, and no node consumes it.
* **Section 2.2.** It flags `f <= H(P)` as a trust surface. That step is now re-derived
  in 4.1 below, from submodularity, including the general splitting form it needs.
* **Section 2.3(3).** Restricting the Bernoulli `G`-shift to an infinite-index free
  subgroup `F` gives a Bernoulli `F`-shift over the base `A^(F\G)`. That base has infinite
  entropy, as stated.
* **External statements.** Adams–Spatzier (Kazhdan groups admit no treeable free ergodic
  actions) and Niblo–Reeves are mentioned, not imported, as marked.

## 4. The f-invariant forces Bernoulli preservation over free groups (gk-p-bernoulli-mass)

Artifact `research/artifacts/free-group-f-invariant-bernoulli-preservation-2026-09-12.md`.

### 4.1 `free-group-injective-ca-preserve-bernoulli-via-f-invariant`. Verdict: PASS, with one lemma generalized.

* **Lemma 2.1 needs the general splitting form.** The artifact proves
  `F(alpha v s alpha) <= F(alpha)`. The ball refinements are not reached by such
  self-splittings. Splitting `beta = alpha^(B_n)` by `s_1` and then by `s_2` produces
  `s_2 s_1 B_n`, which lies outside `B_(n+1)`. The correct passage is
  `alpha^(B_(n+1)) = beta v (join over j, epsilon of s_j^epsilon alpha^(B_n))`: `2r`
  successive splittings `beta' = beta v t gamma`, with `t = s_j^(±1)` and
  `gamma = alpha^(B_n) <= beta`. The same submodularity bound holds for these.
  * Put `d = H(beta v t gamma) - H(beta)`.
  * *Generator `s_i != s_j`.* The term `H(beta' v s_i beta')` grows by at most
    `[H(beta v t gamma) - H(beta)] + [H(s_i beta v s_i t gamma) - H(s_i beta)] = 2d`.
    Adding a partition to a finer base costs less.
  * *Generator `s_j`, `t = s_j`.* `s_j gamma <= s_j beta` absorbs one addition, and the rest
    costs at most `H(s_j beta v s_j^2 gamma) - H(s_j beta) = d`.
  * *Generator `s_j`, `t = s_j^-1`.* `gamma <= beta` absorbs `s_j t gamma`, and the rest
    costs at most `d`.
  * *Total.* `F(beta') - F(beta) <= (1-2r)d + d + 2(r-1)d = 0`.
  So `F(eta^(B_n))` is non-increasing and `f = inf_n F(eta^(B_n))`. This also settles the
  trust surface in Section 2.2 of `rokhlin-lower-bounds-without-finite-models-2026-09-12.md`.
  The author landed the general form in the artifact and route at `152f663f5b`.
* **Invariance.** `tau` is a Borel isomorphism onto `Y`, so `tau^-1 eta` is a finite
  generating partition for `mu` with `f_mu(tau^-1 eta) = f_nu(eta)`. Bowen's independence
  of the generating partition gives `f_nu(eta) = f_mu(eta) = log q`. This is the one
  import (`bowen-f-invariant-citation`), a trust surface.
* **Bernoulli value.** Under `mu`, `F(eta^(B_n)) = log q · ((1-2r)|B_n| + sum_i |T_(n,i)|)
  = log q`, by (4.2).
* **Tree identities.** `s_i B_n` is the ball of radius `n` about `s_i`, and
  `d(e,g) - d(s_i,g) = ±1` in the tree. So `B_n ∩ s_i B_n = B_(n-1) ∪ s_i B_(n-1)`.
  * By symmetry of balls, `|B_n ∩ s_i B_n|` is the number of `s_i`-edges inside `B_n`.
  * A finite subtree has one more vertex than edges, which gives (4.2).
* **Upper bound (4.3).** `H(y_(X∪Y)) + H(y_(X∩Y)) <= H(y_X) + H(y_Y)` applied to coordinate
  sets, with shift invariance. `g eta` is the partition by the coordinate at `g`, so
  `eta^S` is the coordinate window `S`.
* **Induction.** The three steps close exactly as written:
  * `B_0` is forced uniform by `log q <= H(B_0)`;
  * `T_(n-1,i) = D_(n,i)` uniform forces `H(B_n) >= |B_n| log q`;
  * `B_n` uniform forces every `H(T_(n,i))` to its maximum.
  The balls exhaust `G`, so `nu = mu`.
* **Section 5(i).** The inclusion–exclusion counterexample is correct: one bit copied to
  sites `a, b, c` gives left side `log 2` and right side `0`.
* **Trap check.** The invariant is used only for `f_nu = log q`. The separation is done
  on the coordinate partition (data D1), so no conjugacy invariant is being asked to
  separate conjugate systems. Consistent with Section 2.1 above.

## 5. Weak-equivalence invariants are blind to the base (gk-p-inf-cost, `8144951a8c`)

Artifact `research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md`.

### 5.1 `nontrivial-bernoulli-shifts-are-weakly-equivalent`. Verdict: PASS.

* **Freeness (Lemma 1.1).** For `g != 1`, `h != g^-1 h`. A new pair `{h', g^-1 h'}`
  avoids earlier pairs once `h'` avoids finitely many points, so infinitely many disjoint
  pairs exist. Each equality has probability `sum_j lambda(j)^2 < 1`, independently, so
  `Fix(g)` is null.
* **Lemma 2.1, convention check.** With `(g.x)(h) = x(g^-1 h)`, a `W`-cylinder
  `C = {x|_W in S}` has `gC = {y : (g^-1 y)|_W in S}`, which reads `y` on `gW`. So
  `gC_i ∩ C_j` reads `E = W ∪ FW`. Put `Lambda(x)(h) = ell(h^-1 . x)`.
  * `Lambda` is equivariant, `A_i = Lambda^-1(C_i)` and `g A_i = Lambda^-1(g C_i)`.
  * So `mu(g A_i ∩ A_j) = Lambda_* mu (g C_i ∩ C_j)`, which is determined by the law of
    `Lambda(x)|_E`, within `eta` of `lambda^E` in total variation.
  * Step 1 must produce a *partition* `C_1, ..., C_m`: approximate `B_1, ..., B_(m-1)`
    to within `eps/(8m)` and take differences. This is a constant, not a gap.
* **Trust surface.** `fpbs-aw-finite-pattern-input` is worded for a "Bernoulli parameter
  `q`", while the lemma uses an arbitrary `lambda` on `k` symbols. Abért–Weiss cover every
  standard base, so the mathematics stands, but the imported statement should be widened.
  Its reference route also cites `research/artifacts/torsion-actions.md`, whereas the
  artifact field says `research/artifacts/fpbs/torsion-actions.md`.

### 5.2 `cost-is-constant-on-weak-equivalence-classes` (import). Verdict: PASS as an import.

The direction `b ≺ a => C(a) <= C(b)` agrees with Bernoulli shifts having maximal cost,
since `b_lambda ≺ a` for every free `a`. Only constancy on classes is consumed. The
theorem number "Abért–Weiss Theorem 9" is not checked against source, and the
monotonicity itself is Kechris's. That is a trust surface on the citation, not on the
mathematics.

### 5.3 `weak-invariants-give-no-bernoulli-rokhlin-lower-bound`, its refutation and its invalidation. Verdict: PASS.

* **The bound.** `h^Rok(b_lambda) <= H(lambda)` from the time-zero partition, for
  infinite `G`, where the Bernoulli action is ergodic. Then
  `F(Phi_B) <= inf_p H(1-p, p) = 0`.
* **Refutation.** `weak-invariants-bound-bernoulli-rokhlin-entropy-below` asserts a
  positive bound for every `G`, so one group already refutes it. The dead route requires
  exactly that claim.
* **Scope.** Only *base-independent* bounds die. Bounds of the form
  `min{H(lambda), c(G)}` are untouched, and Remark 4.1 records this. Nothing here kills
  a lower bound for `h_sup(G)`.
* **Calibration and remarks.**
  * `F_2` has fixed price 2, and its Bernoulli shifts have sofic entropy `H(lambda)`, so
    the calibration holds.
  * Remark 4.2 uses Hutchcroft–Pete (infimal cost 1 for infinite Kazhdan groups) and
    Gaboriau's `beta_1^(2) <= C - 1`.
  * Remark 4.3 is a no-reduction remark and feeds no node.

## 6. Closure properties of surjunctivity (gk-p-products)

Artifact `research/artifacts/surjunctivity-closure-properties-2026-09-12.md`.

### 6.1 `surjunctivity-is-a-commensurability-invariant` (Theorem A). Verdict: PASS.

* **Conventions.** The automaton reads `x(lambda m)` (right memory) and commutes with left
  shifts. Left multiplication by `H` preserves each right coset `H r_i`, and `g = h r_i`
  uniquely, so `Phi(x)(h) = (x(h r_i))_i` is a homeomorphism `A^G -> (A^n)^H`.
  `Phi(k.x)(h) = x(k^-1 h r_i) = (k.Phi(x))(h)`.
* **Conclusion.** `Phi tau Phi^-1` is continuous, `H`-equivariant and injective, hence a
  cellular automaton over `H` with alphabet `A^n`, by Curtis–Hedlund–Lyndon.
  Surjunctivity of `H` makes it onto.
* **Commensurability.** Follows with heredity to subgroups.

### 6.2 `products-with-lef-factors-preserve-surjunctivity` (Theorem B). Verdict: PASS.

* **Table notion.** The theorem of `strict-pairs-transfer-to-table-realizations` needs
  `phi: F -> K` preserving the products `sm` and `wm` and distinguishing `w != w'` when
  `p(w) != p(w')`, with `F ⊇ {1} ∪ M ∪ S ∪ Omega ∪ SM ∪ Omega M`. An injective map
  preserving every product that lies in `F` supplies both. So the "partial table" of
  Corollary 1 matches.
* **The embedding.** `id x psi` is injective, and it preserves products in `F` because
  `(g,k)(g',k') in F` forces `kk' in F_K`.
* **Surjunctivity of the target.** `G x L ⊇ G x 1` has index `|L|`, so Theorem A applies.

### 6.3 `separated-finite-normal-subgroups-preserve-surjunctivity` (Theorem D). Verdict: PASS.

* **The isomorphism.** `E_0 ∩ N = 1` makes `E_0 -> E_0N/N` an isomorphism onto a
  finite-index subgroup.
* **Transfer.** Both directions follow from heredity plus Theorem A.
* **Equivalence of the hypotheses.** The normal core of `E_0` is a finite-index normal
  subgroup meeting `N` trivially.
* **Corollary D.1.** A splitting over a finite-index subgroup of `Q` gives such an `E_0`.

### 6.4 `graph-product-closure-from-product-closure`. Verdict: PASS as a conditional route.

* **Amalgam.** `Gamma(X) = Gamma(st v) *_(Gamma(lk v)) Gamma(X∖v)` is standard. Full
  subgraph products are retracts, so both edge maps are injective.
* **Graph folds.** `(rho_(st v), rho_(X∖v))` restricts to the identity on each vertex
  group. So the two-vertex graph of groups satisfies the hypothesis of
  `graph-folds-over-surjunctive-groups-are-surjunctive`: injective edge maps, and a
  homomorphism to a surjunctive group injective on each vertex group.
* **Target.** The target is surjunctive by induction plus the open product closure.
* **Infinite graphs.** Surjunctivity is local, and every finitely generated subgroup lies
  in some finite full subgraph product.
* **Proposition C.** Part (a), all products via separating projections and table
  transfer, holds. So does the quasivariety form: Mal'cev's characterization applies to a
  class containing the trivial algebra and closed under `I, S, P, P_U`.

### 6.5 Quotient closure. Verdict: wiring correct.

`gottschalk-via-quotient-closure` requires the open `surjunctivity-passes-to-quotients`.
The converse route requires the goal. The cycle cannot fire.

## 7. The peeling boundary (gk-p-tails)

Artifact `research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md`.

### 7.1 `own-block-local-bijection-rows-peel`. Verdict: the lemma PASSES; the nonlinear instance is FALSE and is withdrawn.

* **Lemma 1.1.**
  * `E(X,Y) = (Phi_Y(X), Y)` is a bijective CA, `D = F E^-1` has the form
    `(Z, T_Z(Y))`, and `T_0 = F'`. `F'` is injective because `D` is.
  * `F` is surjective iff `D` is, and `D` is surjective iff `T_0` is. The `<=` direction
    is `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`. I re-derived it:
    - if `T_0` is bijective and `Z` has finite support, `T_0^-1 T_Z` is injective and
      rewrites `Y` only on a finite set, by a rule reading a finite set, so it permutes
      each fibre and is onto;
    - for general `Z`, approximate by finitely supported `Z_n`. Preimages under `T_(Z_n)`
      converge along a subsequence to a preimage under `T_Z`.
* **Redundant hypothesis.** The "uniformly bounded local inverse" is automatic once every
  `Phi_Y` is bijective: `E` is then a bijective CA, and its inverse is a CA by
  compactness.
* **False instance (artifact Section 1 "Example", and the graded-nilpotent sentences in
  the claim and its route).**
  * `row(x)(g) = x(g) + x(g+1) x(g+2)` over `F_2` is not injective: the constant
    configurations `0` and `1` both map to `0`.
  * `N(x)(g) = x(g+1)x(g+2)` is not nilpotent under composition:
    `N(N(x))(g) = x(g+2)x(g+3)x(g+4)`.
  * For nonlinear `N`, `sum_(k<D) (-N)^(k)` is not an inverse of `I + N`, even when
    `N o N = 0`, because `(I+N)(x - N(x)) = x - N(x) + N(x - N(x))`.
  * *Correct nonlinear instances:* compositions of track shears inside the block,
    `(u,v) -> (u + f(v, Y), v)` and `(u,v) -> (u, v + h(u, Y))` with arbitrary local `f`
    and `h`. Their inverses are the opposite shears.

### 7.2 `peeling-to-surjunctive-memory-tail-forces-surjectivity`. Verdict: PASS.

The tail acts coset by coset over `H` (`surjunctivity-passes-to-subgroups`). Lemma 1.1
carries surjectivity back up the chain.

### 7.3 `strict-three-factor-needs-noninvertible-own-block`. Verdict: PASS.

* **Proof.** Theorem 3.1 is the contrapositive of Corollary 1.2.
* **Dichotomy.** B1/B3 is the linear/nonlinear split of the non-bijective own parts. "Each
  already an open direct-finiteness question" describes the minimal instances, not every
  B3 row.
* **Wiring.** The route requires
  `central-c3-quadratic-surjunctivity-iff-direct-finiteness`, which the proof of Theorem
  3.1 does not use. That is harmless.

## 8. Weak soficity as a chart supply (gk-free-pos)

Artifact `research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md`.
`weakly-sofic-groups-are-surjunctive` stays OPEN, correctly.

### 8.1 `regular-action-makes-weak-sofic-defects-maximal`. Verdict: the computation PASSES; the consequence is overstated and corrected.

* **Computation.** `fix(z) = 0` for `z != 1`, so `l_V` is discrete.
* **Consequence.** Lemma 1.1 is a *sufficient* condition for the transported identity at
  `v`. For a nontrivial defect it fails at every vertex. That removes the Gromov–Weiss
  guarantee, and Corollary A.1 is right: the defect hypothesis of Proposition 1.2 with
  `delta < 1` holds iff every defect is trivial. It does not show that the identity
  *fails* anywhere, since the rules may ignore the moved coordinates or agree there by
  symmetry. So the claim's "holds at a positive fraction of vertices only if every
  multiplicative defect is trivial", and the route's "so the identity fails at every
  vertex", overstate.
* **Convention.** With `tau_V(z)(v) = mu((z(phi(m)v))_m)`, the composite reads `z` at
  `phi(m)phi(n)v`. So the chart models the opposite group, and Lemma 1.1's condition has
  its factors in the other order. That is harmless, via inversion.

### 8.2 `simple-model-weak-soficity-with-small-defect-is-lef`. Verdict: PASS.

* **Chain.** `S_n = S_(n+1)` forces `S_(n+2) = S_(n+1)`, so the chain reaches `H` within
  `|H|` steps.
* **Bound.** `l(x) <= |H| l(k)` follows by subadditivity and conjugation invariance.
* **Injectivity.** Injectivity of `phi_F` needs the approximation on a set containing
  `F^-1 F`, so that `phi(g)^-1 phi(g') = phi(g^-1 g')` is available. Approximations exist
  for every finite set, so this is harmless.
* **LEF implies sofic.** Via the regular action.

### 8.3 Lemma 5.1 (coset decomposition of permutation lengths). Verdict: PASS.

`l_V = sum_i p_i l_(H/L_i)` over orbits. Disjoint unions realize exactly the *rational*
convex combinations. The linear program of Corollary 5.2 has rational data, so
feasibility is unaffected.

### 8.4 Proposition 1.2, second half (author's pressure point). Verdict: the constant needs the defect.

A chart fails at `v` when `v` is fixed by `phi(b)^-1 phi(a)`. The inversion defect
`phi(b)phi(b^-1) phi(1)^-1` and the multiplication defect `phi(b)phi(b^-1 a) phi(a)^-1` both
have `l_V <= delta`. So
`l_V(phi(b)^-1 phi(a)) >= l_V(phi(b^-1 a)) - 2 delta >= c' - 2 delta`, by subadditivity and
conjugation invariance of `l_V`.

The union bound then gives injective charts on at least a `1 - |K|^2 (1 - c' + 2 delta)`
fraction of vertices, not `1 - |K|^2 (1 - c')`. No node consumes the constant. The `|H|`-step
bound in Theorem B is enough for the claim as stated, so no covering-number citation is
needed.

## 9. Borel invariants and the alphabet-size target (gk-p-inf-wild)

Artifact `research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md`.

* **`borel-structurability-invariants-are-bernoulli-base-blind`: PASS.**
  * The symbol inclusion `2^G -> q^G` preserves stabilizers, so it sends free points to
    free points.
  * An equivariant map between free actions is bijective from each orbit onto an orbit.
  * With the Seward–Tucker-Drob import, `J` is constant. The import is a trust surface,
    read from the abstract.
* **`alphabet-conjugacy-invariance-from-gottschalk`: valid.** `iota o phi` is an
  injective CA with image in the proper closed set `iota(B^G)`.
* **`alphabet-conjugacy-invariance-from-bernoulli-maximality`: valid.**
  `h^Rok(A^G, mu) = h^Rok(B^G, nu) <= log|B|`, because the time-zero partition generates.
* **`full-shifts-with-different-alphabets-are-not-conjugate`: OPEN, correctly.**
* **Section 4.** Context remarks only.

## 10. Popa deformation/rigidity (gk-p-bernoulli-popa)

Artifact `research/artifacts/popa-deformation-rigidity-and-bernoulli-preservation-2026-09-12.md`.
`deformation-rigidity-gives-no-coordinate-level-bernoulli-input`: PASS as scoped.

* **Item 1.** A missing pattern appears almost surely by Borel–Cantelli over disjoint
  translates, so `mu(Y) = 0` and `nu` is singular. A deformation defined on the measure
  algebra of `mu x mu` does not act on singular joinings.
* **Item 2.**
  * *The strict injection.* `psi(gH) = g u^-1 H` is well defined because
    `u H u^-1 <= H`, and it is non-injective because the inclusion is strict. So
    `y -> y o psi` is a strict continuous equivariant injection, whose image (constant on
    the fibres of `psi`) is product-null.
  * *The hypotheses hold.* The generalized Bernoulli shift over `G/H` is s-malleable by
    coordinatewise rotation, and weakly mixing on `G` because `G/H` is one infinite
    orbit. These are exactly the hypotheses of Popa's cocycle superrigidity, so the
    calibration is honest. The theorem's truth is not used.
* **Item 3.** The edges `{g, gs}`, `g in F`, lie inside copies of `Z`, so they form a
  forest. The incidence map is onto `F_2^F` and pushes uniform to uniform, and the kernel
  consists of the configurations constant on cosets `g<s>`.
* **Section 4.** A remark with a stated trust surface, and it feeds no node.

## 11. Permutational wreath products and stabilizer products (gk-n-ff, `06a4ab7213`)

Artifact `research/artifacts/wreath-surjunctivity-stabilizer-products-2026-09-12.md`, which builds
on [W] = `research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md` (passed in Section 1 of
`gk-verify-pos-permanence-chain-2026-09-12.md`).

`wreath-surjunctivity-reduces-to-stabilizer-products`: PASS. This is a closure theorem, so every
point the author flagged was re-derived.

* **Only if.**
  * For `h in G_U` and `n` supported in `U`, `(h.n)(x) = n(h^-1 x)`. This equals `n(x)` on `U`,
    and `h^-1` permutes `X∖U`, so `h.n = n`.
  * `A^U` and `G_U` therefore commute and meet trivially, so `A^U x G_U <= W`. Heredity finishes.
* **Separating family.**
  * `H_S = {(n,1) : n|_S = 1}` is a subgroup, and `H_S w = H_S w'` iff `w' w^-1 in H_S`.
  * Distinct `w, w'` have `w' w^-1` either outside `N`, or equal to `(n'n^-1, 1) != 1`, and taking
    `S` to contain the support kills that case.
  * [W, Lemma 1.2] needs only this property, so no finite quotient of `A` is used.
* **Coordinates.**
  * Put `(n',g')(n,g)^-1 = (n'·(g'g^-1).n^-1, g'g^-1)`. It lies in `H_S` iff `g = g'` and
    `n|_S = n'|_S`, so `H_S\W = A^S x G`.
  * The right action is `(a,g).(n_1,g_1) = (a·nu_(n_1)(g), g g_1)`.
  * Read as the direct product `Lambda_U = A^U x G`, the transplant reads `y(lambda p_m(g))` with
    `p_m(g) = (nu_(n_m)(g)|_U, g_m)`. `nu_(n_m)(g)|_U` takes values in `values(n_m) ∪ {1}` on the
    finite set `U`, so `P_U` is finite.
* **Invariance.**
  * For `k = (b,h) in K_U = A^U x G_U`, `p_m(hg) = p_m(g)`, because `h^-1 s = s` on `U`.
  * Translation in the `A^U` coordinate commutes with `tau_U` directly.
  * Slicewise extensions of maps commuting with `A^(U') x G_(U')` commute with `K_U`, so [W]
    Proposition 4.1(c) holds with `K_U`.
* **Region.**
  * `Z_s` is a finite union of right `G_s`-cosets ([W, Lemma 2.2]).
  * An intersection over `s in U` of right cosets of the `G_s` is empty or a right `G_U`-coset.
    So `Q_U` is a finite union of right `G_U`-cosets.
  * Then `A^U x G_U h_i = K_U (1, h_i)`, since `A^U` lies in `K_U`.
* **Coset-region lemma.** [W, Lemma 3.1] is stated for `K <= G`, but its proof uses only:
  * a surjunctive subgroup `K` of an ambient group;
  * a region that is a finite union of right `K`-cosets, which stays so under right
    multiplication by the finite memory;
  * left-`K`-invariant rules.
  All three hold for `K_U <= Lambda_U`. At `lambda = k(1,h_i)` the selected memory is
  `p_m(h h_i) = p_m(h_i)`, which depends only on `i`, so `Psi` is a CA over `K_U`.
* **Base case.** `Lambda_empty = K_empty = G`.
* **Consequences.** `A wr G` is surjunctive iff `G` and every `A^n` are. Sofic lamps over sofic
  bases give surjunctive wreath products for every action, since `A^U x G_U` is sofic.

## 12. Property (T) and superrigidity on strict pairs (gk-p-inf-kazhdan, `0ee6dfac3f`)

Artifact `research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md`.

* **`fg-infinite-simple-groups-are-minimally-almost-periodic`: PASS.**
  * Peter–Weyl detects a nontrivial compact image in some `U(d)`.
  * The image is finitely generated linear, hence residually finite (Malcev).
  * Simplicity makes the representation injective.
  * An infinite residually finite group has a proper nontrivial finite-index normal subgroup,
    which a simple group lacks.
* **`popa-bernoulli-cocycle-superrigidity` (import): PASS as an import, with a trust surface.**
  * The quoted hypotheses and the `U_fin` class match the abstract of Popa, Invent. Math. 170
    (2007): an infinite normal subgroup with relative (T), and targets in closed subgroups of
    unitary groups of separable II_1 factors.
  * *Trust surface.* The abstract's example is `[0,1]^G`. The consumer uses atomic bases
    `A^G`, so whether Theorem 0.1 covers every nontrivial base, directly or through the passage
    to relatively weakly mixing quotients, must be read at source. Theorem 4.1's scope inherits
    this.
* **`kazhdan-map-bernoulli-finite-extensions-are-trivial` (Theorem 4.1): PASS, given the import.**
  * *Multiplicity and sheets.* `n(x) = |supp m_x|` is invariant, since `g_* m_x = m_(gx)`, and so
    constant by ergodicity. Lusin–Novikov enumerates the finite fibres.
  * *Cocycle.* The action is `(x,i) -> (gx, c(g,x)(i))`. The conditional weights need not be
    uniform, which is harmless.
  * *Untwisting.* Superrigidity gives `rho`, trivial because there are no finite quotients.
    `Phi(x,i) = (x, f(x)^-1 i)` makes each sheet invariant.
  * *Ergodicity.* Every sheet has positive measure, since atoms carry positive conditional mass,
    so `n = 1`.
* **`strict-pair-flip-lifts-are-relatively-weakly-mixing` (Proposition 5.1): PASS.**
  * *Intermediate factor.* `sigma o F = pr_1` places `(A^G, nu)` between `Omega` and the base.
    `F_* P_x` is supported on `sigma^-1(x)` and integrates to `nu`, so it is the disintegration.
  * *Relative products.* `(F x F)_*(P_x x P_x) = nu_x x nu_x`, so the relative product of the
    lift is a factor of `X x Y x Y`. That is ergodic, as ergodic times weakly mixing.
* **Section 5.4.** The inequality holds:
  * `|F'| log q <= H(P^(F'F)) + |F'| eps` by independence of the `g.C`, each `eps`-determined by
    `P^(gF)`;
  * `H(P^(F'F)) <= |F'F| H(P)`.
  The decay `<= (1+c)^-r log q` holds whenever `F` contains `S^r`. "Tends to 0 as the window
  grows" is informal, since `F` need not contain large balls. It is a mechanism analysis, and
  no node consumes it.

## 13. Direct arguments on simple hosts (gk-p-simple-direct)

Artifact `research/artifacts/simple-host-direct-attack-2026-09-12.md`. All five claims PASS.

* **`site-pullbacks-strict-iff-stabilizer-self-compressed`.**
  * *Site maps.* `psi_c(gK) = gcK` is well defined iff `c^-1 K c <= K`. It is injective iff
    `cKc^-1 <= K`, hence iff `cKc^-1 = K`.
  * *One-site maps.* A nonconstant one-site map reading `p` at `o` forces `K` to fix `p`: two
    configurations differing only at `k^-1 p` would otherwise give different values.
  * *Strictness.* The pullback is onto iff `psi_c` is injective.
  * *Finite `K`.* It admits no proper self-conjugation.
* **`surjectivity-descends-to-centralized-coset-quotients`.**
  * `tau R_b = R_b tau` because `mb = bm`.
  * `N_G(B)/B` acts freely from the right on `G/B`, and `M` lies in `C_G(B) <= N_G(B)`, so reads
    stay inside each right orbit.
  * The restriction to `Y_B` is a product of copies of `taubar`.
  * If `tau` is bijective, the preimage of a `B`-invariant configuration is `B`-invariant.
* **`strict-automata-closed-under-host-manipulations`.**
  * *Conjugation.* `R_c tau R_(c^-1)(x)(g) = mu((x(gcmc^-1))_m)`.
  * *Transport.* Restriction to `alpha(G)` plus heredity.
  * *Composites.* The image of `tau o rho` lies in `tau(A^G)`. The image of `rho o tau` is proper
    both when `rho` is onto and when it is not.
  * *On `R^x`.* The doubling `g -> s0 g t0 + s1 g t1` is an injective homomorphism, via
    `t_i s_j = delta_ij` and `t0 (.) s0`.
* **`surjunctivity-iff-automaton-monoid-directly-finite`.**
  * The continuous inverse on the image extends to a CA left inverse.
  * *Iterates.* `X_(n+1) = X_n` would give `X_1 = sigma^n(X_(n+1)) = sigma^n(X_n) = A^G`.
  * *Attractor.* `tau` is onto `X_inf` because `sigma(y)` lies in every `X_(n-1)`.
* **`invariant-output-symmetry-must-be-core-free`.**
  * `tau(n^-1 . x)(g) = tau(x)(ng) = tau(x)(g(g^-1 n g)) = tau(x)(g)`.
  * Injectivity plus freeness of the full shift forces `n = 1`.

## 14. Revision of the wreath artifact (gk-n-ff, blob `d4f40101ca`)

The revised text of `wreath-surjunctivity-stabilizer-products-2026-09-12.md` makes explicit the
points Section 11 had re-derived. Verdict: PASS.

* **Lemma 3.1 in the ambient group.** Lemma 3.1 is read over `Lambda_U` with alphabet `B`. Its
  proof uses only a subgroup of an ambient group and a finite alphabet.
* **The window region.** `F_U` is built from the `G`-projections of the memories, because every
  condition in the window argument (membership in `Z_s` or `Q_(U')`) concerns only the `G`
  coordinate.
* **Invariance of the rules.** The lemma is applied to `rho_U` through left `K_U`-invariance of
  its rules. A finite-memory `rho` commuting with `l_k` has `mu_(k lambda) = mu_lambda`: the
  points `lambda p` are distinct, so `y|_(lambda P)` ranges over all patterns. The earlier text
  used `tau_U`'s memory at this step.
* **Slicewise extensions.** `(k.y)_lambda = (c,h).y_(d^-1 lambda)` for `k = ((c,d),h)`, so they
  commute with `A^(U') x A^(U∖U') x G_(U')`.
* **Compatibility remark.** It is right: `A^U` is LEF when `A` is, so
  `products-with-lef-factors-preserve-surjunctivity` plus heredity gives every `A^U x G_U`.

## 15. Alphabet size under conjugacy is elementary (gk-p-inf-wild, Proposition 3.0)

`full-shifts-with-different-alphabets-are-not-conjugate` is now ESTABLISHED by
`full-shifts-with-different-alphabets-are-not-conjugate-proof`. Verdict: PASS.

* **The count.** `x` is fixed by all of `G` iff `x(h) = x(g^-1 h)` for all `g` and `h`, i.e. iff
  `x` is constant. An equivariant map sends fixed points to fixed points. So an equivariant
  injection gives `|A| <= |B|`, with no continuity used.
* **Honest correction.** The node records its own correction: it had been landed as OPEN and
  called a "sharp negative target". The two alphabet routes stay valid but redundant, and nothing
  premature follows from either.
* **Measurable form.** The content-bearing version, where fixed points are null, is
  `measurable-alphabet-compression-over-leavitt-units`. That claim is not verified here.

## 16. Wreath closure equals product closure (gk-p-products)

* **`wreath-closure-from-product-closure`: valid conditional route.** Product closure makes `A^U`
  and then `A^U x G_U` surjunctive, and `G_U <= G` is surjunctive by heredity. The
  stabilizer-product theorem (Section 11) finishes.
* **`product-closure-from-wreath-closure`: valid.** Over a one-point set with trivial action,
  `N = A`, `G` acts trivially, and `A wr_(pt) G = A x G`.
* **`permutational-wreaths-of-surjunctive-groups-are-surjunctive`: OPEN, correctly.** The cycle
  passes through the open product-closure claim and cannot fire.

## 17. Author follow-ups on the corrections (gk-p-tails `8b6443da85`, gk-free-pos `f0270128be`)

* **gk-p-tails, replacement instance.** `x(h) + x(h)x(ht) + x(ht)x(ht^2)` over `F_2`, with `t` of
  order three. Verdict: PASS.
  * On each left coset of `<t>`, with `(a,b,c) = (x(h), x(ht), x(ht^2))`, it acts as
    `(a,b,c) -> (a+ab+bc, b+bc+ca, c+ca+ab)`, using `ht^3 = h`.
  * Evaluating all eight vectors: `000, 100, 010, 001, 111` are fixed, and
    `110 -> 011 -> 101 -> 110`. So the map permutes `F_2^3` on every coset, and the row is a
    nonlinear own-block local bijection.
  * Its inverse is local by compactness.
  * The track shears are correctly marked as adding no scope beyond type (O).
* **gk-free-pos, transport convention and constant.** Verdict: PASS.
  * Transporting along `psi(g) = phi(g^-1)` gives `sigma_V tau_V(z)(v) = z(v)` whenever
    `psi(m)psi(n)v = psi(nm)v` for all `n` in `N` and `m` in `M`. Put `x(g) = z(psi(g)v)` on
    `NM ∪ {1}`: the local identity holds for every pattern, including constrained ones, and
    `psi(1) = 1`.
  * `psi(m)psi(n)psi(nm)^-1` is `phi`'s defect at `(m^-1, n^-1)`, so symmetric `F` suffices.
  * The constant `1 - |K|^2(1 - c' + 2 delta)` with `KK^-1` in `F` matches Section 8.4.

## 18. Theorem 4.1, step 0 (gk-p-inf-kazhdan `3300ce782d`), and a coverage index

* **Step 0 (base reduction). Verdict: PASS.** It discharges the Section 12 trust surface.
  * `(X_0 x [0,1], mu_0 (x) Leb)` is standard and atomless, so it is isomorphic to `([0,1], Leb)`.
    Coordinatewise, `X x Y = ([0,1], Leb)^G` equivariantly.
  * `Z x Y` is ergodic, as ergodic times weakly mixing.
  * `pi x id` has conditional measures `m_x (x) delta_y`, so the multiplicity is unchanged, and it
    is an isomorphism iff `pi` is.
  * So `popa-bernoulli-cocycle-superrigidity` is consumed only for the s-malleable diffuse-base
    shift, which is the form it now states. `G` infinite is added.
  * The Section 5.4 cap (at most `(1+c)^-r log q` on windows containing a translate of `S^r`)
    replaces the informal decay.
* **Imports covered above, named for search.**
  * `bowen-f-invariant-is-a-measure-conjugacy-invariant` (Section 4.1, one trust surface);
  * `seward-tucker-drob-free-borel-actions-map-to-2-shift` (Section 9, read from the abstract);
  * `cost-weak-containment-monotonicity-citation` (Section 5.2);
  * `popa-bernoulli-cocycle-superrigidity-citation` (Sections 12 and 18).
* **Other ids covered above.**
  * `positive-rokhlin-entropy-via-weak-invariant-bounds` is correctly invalidated (Section 5.3).
  * `permutation-lengths-are-convex-hulls-of-coset-lengths` is Lemma 5.1 (Section 8.3).
  * `product-closure-from-graph-product-closure` and `quotient-closure-from-gottschalk` are
    deliberate equivalence cycles through open claims (Sections 6.4 and 6.5).
* **Open claims whose wiring was checked.** Merges since 12:35 removed no status line and added
  no route that can fire.
  * `fg-simple-kazhdan-groups-are-surjunctive`
  * `every-group-has-positive-rokhlin-entropy-action`
  * `leavitt-unit-group-has-positive-rokhlin-entropy-action`
  * `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`
  * `finite-direct-products-of-surjunctive-groups-are-surjunctive`
  * `graph-products-of-surjunctive-groups-are-surjunctive`
  * `finite-normal-subgroups-do-not-affect-surjunctivity`
  * `every-injective-ca-preserves-uniform-bernoulli-measure`
  * `injective-cas-over-leavitt-units-preserve-uniform-bernoulli`
  Since 12:35 only two new routes target the goal: `gottschalk-via-binary-alphabet-descent` and
  `gottschalk-via-quotient-closure`. Both require open claims.
* **gk-free-wild filters.** `cubulated-hyperbolic-table-cores-carry-no-strict-pair` and
  `mixed-bigon-difference-graphs-present-vh-square-complexes` already cite
  `gk-vf-nonlinear-verification-2026-09-12.md`, so they are left to that verifier.
  * I checked the consumed chain once. Agol plus Haglund–Wise make hyperbolic cubulated groups
    virtually special, hence linear over `Z` and residually finite. A residually finite core is
    sofic, contradicting `forward-relations-of-a-counterexample-have-a-nonsofic-core`.

## 19. gk-p-inf-cost revision (`d4b2e9bbc3`)

Verdict: PASS. This re-checks the changed dependency.

* **`nontrivial-bernoulli-weak-equivalence-proof`.** It now has `requires: []` and quotes
  Abért–Weiss Theorem 1: a free p.m.p. action of a countably infinite group weakly contains every
  Bernoulli action `kappa^Gamma`, for any probability space `kappa`. That covers finite bases
  directly.
  * Freeness (Lemma 1.1) together with Theorem 1 applied in both directions gives weak equivalence.
  * The Section 5.1 trust note about the narrow `fpbs-aw-finite-pattern-input` no longer bears on
    this route.
* **Cost monotonicity.** It is now attributed to Kechris (Corollary 10.14, as Abért–Weiss print it)
  and scoped to finitely generated groups, which is its published scope.
  * The blindness claim's cost instance inherits "finitely generated". Its weak-equivalence and
    group-invariant parts do not use it.
  * Every INF host is finitely generated, so no conclusion changes.
* **Path.** `fpbs-aw-finite-pattern-reference` now points to `research/artifacts/fpbs/torsion-actions.md`.
