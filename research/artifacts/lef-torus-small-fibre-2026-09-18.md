# LEF groups are torus-surjunctive: a dimension-free small-fibre lemma (2026-09-18)

Agent: swarm-0917-w10-w10-gs-follow. Lane: follow-through toward
`gottschalk-surjunctivity-conjecture`, on the last-missing hole
`injective-torus-automata-have-regular-degree` (C2 of
`gottschalk-via-torus-alphabet-degree-transfer`).

## 0. Summary

- **Theorem 1 (small-fibre lemma).** For every `N >= 1`, a continuous map
  `f: T^N -> T^N` whose fibres have sup-metric diameter at most `1/16` is onto, and
  `f^*` is an automorphism of `H^1(T^N; Z) = Z^N`. The constant does not depend on `N`.
- **Theorem 2.** Let `G` be LEF (every finite subset admits an injective partial
  homomorphism into a finite group). Then for every `d` and every injective continuous
  `G`-equivariant `tau: (T^d)^G -> (T^d)^G`:
  - in every sufficiently fine LEF model `phi: K -> Q`, the matrix `phi(D)` is invertible
    in `M_d(Z[Q])`;
  - `D = D(tau)` is a two-sided non-zero-divisor in `M_d(Q[G])` (so C2 holds);
  - `tau` is onto, hence a homeomorphism (by the established degree lemma C1).
- **Belief changes.**
  - Two recorded "smallest open hosts" for torus surjunctivity (TS) fall: `Q/Z`,
    `Z(2^inf) x Z(3^inf)` (wave 9) and `Alt_fin(N)` (wave 10). They are locally finite,
    hence LEF. The Bezout witness `s + s^2 - t` never occurs as the degree of an injective
    automaton over any LEF group.
  - The wave-9 conclusion "C2 and TS are open where Gottschalk is trivial" is false on
    every locally finite group. TS now holds on exactly the class where Gottschalk is
    proved by exact finite models (LEF). The heuristic behind
    `gottschalk-via-torus-alphabet-degree-transfer` is restored at that level.
  - New hosts beyond everything previously recorded: every locally finite group, and
    finitely generated LEF groups that are not residually finite, for example
    `FSym(Z) ⋊ Z` (Section 4).
- **Obstruction (Theorem 3).** A small-fibre lemma cannot tolerate even one defective
  coordinate. So the step from LEF to sofic groups cannot be a statement about the finite
  model map alone; it must use locality at the defects.

## 1. Notation

- `T = R/Z`, `||t||` = distance to the nearest integer. On `T^N` use the sup metric
  `rho(u, v) = max_i ||u_i - v_i||`. On `(T^d)^S` use the sup over `S x {1..d}`.
- For `u, v in T^N` with `rho(u, v) < 1/2`, the **displacement** `delta(u, v)` is the
  unique vector in `R^N` of sup norm `< 1/2` that projects to `v - u`. Displacements add:
  if `|delta(u,v)| + |delta(v,w)| < 1/2` then `delta(u,w) = delta(u,v) + delta(v,w)`.
- Conventions for `X_d = (T^d)^G` as in `research/artifacts/torus-alphabet-degree-2026-09-17.md`,
  Section 0: shift `(h x)_g = x_(h^-1 g)`, basis `e_(g,i) = g e_i` of
  `H^1(X_d) = Z[G]^d`, and `tau^*(xi) = xi D` with row `i` of `D` the class of
  `x -> tau(x)_(1,i)`.
- An equivariant `tau` is `tau(x)_g = mu(g^-1 x)`, where `mu = ev_1 o tau: X_d -> T^d`.
- **LEF.** `G` is locally embeddable into finite groups if for every finite `K <= G`
  (subset) there are a finite group `Q` and an injective `phi: K -> Q` with
  `phi(ab) = phi(a) phi(b)` whenever `a, b, ab in K`. Then `phi(1) = 1` if `1 in K`.
  Residually finite groups, locally finite groups and abelian groups are LEF, and LEF is
  a local property.

## 2. Theorem 1: small fibres force surjectivity and an H^1 isomorphism

**Theorem 1.** Let `N >= 1` and let `f: T^N -> T^N` be continuous with
`f(u) = f(v) => rho(u, v) <= 1/16`. Then `f` is onto and `f^*: H^1(T^N; Z) -> H^1(T^N; Z)`
is bijective.

*Step 1 (modulus).* There is `eta > 0` with `rho(f(u), f(v)) < eta => rho(u, v) < 1/8`.
Otherwise take `u_k, v_k` with `rho(f u_k, f v_k) -> 0` and `rho(u_k, v_k) >= 1/8`, and
pass to convergent subsequences `u_k -> u`, `v_k -> v`. Then `f(u) = f(v)` and
`rho(u, v) >= 1/8`, against the hypothesis.

*Step 2 (a coarse inverse on a neighbourhood of the image).* Let `Z = f(T^N)`, compact.
Fix a set `P` disjoint from `Z`: either empty, or a single point `p not in Z`. Choose
`0 < r < eta/2` with `r < dist(P, Z)` (no condition if `P` is empty). Cover `Z` by
finitely many open balls `B_1, ..., B_m` of radius `r` centred at points `z_i in Z`, and
put `O = B_1 ∪ ... ∪ B_m`, an open set disjoint from `P`. Choose `x_i in f^-1(z_i)`.
- If `B_i ∩ B_j` is nonempty then `rho(z_i, z_j) < 2r < eta`, so `rho(x_i, x_j) < 1/8`,
  and `delta_(ij) := delta(x_i, x_j)` is defined, of norm `< 1/8`.
- Partition of unity: `nu_i(z) = dist(z, T^N \ B_i)` is positive exactly on `B_i`; put
  `lambda_i = nu_i / sum_j nu_j` on `O`.
- On `B_(i0)` define `h(z) = x_(i0) + sum_i lambda_i(z) delta_(i0 i)`, the sum over the
  `i` with `B_i ∩ B_(i0)` nonempty (all other `lambda_i` vanish on `B_(i0)`). It is
  continuous on `B_(i0)`.
- The definitions agree on overlaps. Let `z in B_(i0) ∩ B_(i1)` and `lambda_i(z) > 0`.
  All three balls contain `z` and the displacements have norm `< 1/8`, so
  `delta_(i0 i) = delta_(i0 i1) + delta_(i1 i)` by additivity (`1/8 + 1/8 < 1/2`). Since
  `sum_i lambda_i = 1`,
  `x_(i0) + sum lambda_i delta_(i0 i) = (x_(i0) + delta_(i0 i1)) + sum lambda_i delta_(i1 i) = x_(i1) + sum lambda_i delta_(i1 i)`.
- So `h: O -> T^N` is a well-defined continuous map.

*Step 3 (`h o f` is homotopic to the identity).* Let `u in T^N` and `z = f(u)`.
- For every `i` with `lambda_i(z) > 0` we have `rho(z, z_i) < r < eta`, so
  `rho(u, x_i) < 1/8`.
- Fix one such `i0` and put `e = delta(u, x_(i0))`. For each such `i`, `e + delta_(i0 i)`
  has norm `< 1/4` and projects to `x_i - u`.
- Hence `h(f(u)) = u + Delta(u)` with `Delta(u) = sum_i lambda_i(z) (e + delta_(i0 i))`,
  a convex combination of vectors of norm `< 1/4`.
- So `rho(h f(u), u) < 1/4`, and `Delta(u) = delta(u, h f(u))` is continuous in `u`.
- The straight-line homotopy `H_t(u) = u + t Delta(u)` joins `id` to `h o f`.

*Step 4 (surjectivity).* Suppose `f` is not onto. Pick `p not in Z` and `P = {p}` in
Step 2. Then `id_(T^N) ≃ h o f`, with `f: T^N -> O` and `h: O -> T^N`, so the identity of
`H^N(T^N; Q) = Q` factors through `H^N(O; Q)`.
- Every component of `O` is a connected open subset of `T^N` that misses `p`. It is not
  closed in the connected `T^N`, so it is not compact: it is a connected noncompact
  `N`-manifold.
- Hatcher, *Algebraic Topology*, Proposition 3.29: "If M is a connected noncompact
  n-manifold, then H_i(M;R) = 0 for i ≥ n." So `H_N(O; Q) = 0`.
- By universal coefficients over the field `Q`, `H^N(O; Q) = Hom(H_N(O; Q), Q) = 0`.
- The identity of `Q` would factor through `0`, a contradiction. So `f` is onto.

*Step 5 (H^1).* Now `Z = T^N`. Take `P` empty, so `O = T^N` and `h: T^N -> T^N` with
`h o f ≃ id`. Hence `f^* o h^* = id` on `H^1(T^N; Z) = Z^N`, so `f^*` is onto. A surjective
endomorphism of `Z^N` is injective: the sequence `0 -> ker -> Z^N -> Z^N -> 0` splits, so
`ker` has rank `0` and is a subgroup of `Z^N`, hence `0`. QED.

*Remarks.*
- The constant `1/16` is used only through `1/8 + 1/8 < 1/2`. Nothing depends on `N`,
  and this is the point. Invariance of domain needs an injective map. Here the map is only
  injective up to `1/16`, in all coordinates at once.
- The same proof works for self-maps of `M^N`, with `M` a closed connected Riemannian
  manifold and fibres below a fixed fraction of its convexity radius. It uses centres of
  mass coordinatewise and `Z/2` coefficients in Step 4. That extension is not used and not
  claimed here.

## 3. Theorem 2: exact finite models of an injective torus automaton

Fix `G`, `d` and an injective continuous equivariant `tau: X_d -> X_d`, with
`mu = ev_1 o tau` and degree matrix `D`.

**Lemma A (uniform injectivity).** For every `eps > 0` there are a finite `W <= G` with
`1 in W` and `eta > 0` such that for all `x, y in X_d`:
`max_(w in W) rho(tau(x)_w, tau(y)_w) < eta  =>  rho(x_1, y_1) < eps`.

*Proof.* `X_d` is compact and `tau` injective, so `tau: X_d -> tau(X_d)` is a
homeomorphism and `ev_1 o tau^-1: tau(X_d) -> T^d` is uniformly continuous for the product
uniformity. A basic entourage of the product uniformity is "`eta`-close on a finite set
`W`". QED.

**Lemma B (finite-memory approximation).** For every `eps_1 > 0` there are a finite
`F <= G` with `1 in F` and a continuous `mu': (T^d)^F -> T^d` with
`rho(mu(x), mu'(x|_F)) < eps_1` for all `x`. If `eps_1 < 1/2`, the degree data agree:
row `i` of `D` is the `H^1` class of `x -> mu'(x|_F)_i`, so `supp D <= F`, and writing
`mu'^*(e_i) = sum_(f in F, j) c_(i,f,j) e_(f,j)` in `H^1((T^d)^F) = Z^(dF)` we get
`D_(ij) = sum_f c_(i,f,j) f`.

*Proof.* By uniform continuity of `mu` there are a finite `F` and `delta > 0` with:
`x|_F`, `y|_F` `delta`-close implies `rho(mu(x), mu(y)) < eps_1`. Put
`mu'(p) = mu(p ∪ 0)`, extending `p` by `0` off `F`. Then `x` and `x|_F ∪ 0` agree on
`F`. For `eps_1 < 1/2` the straight-line homotopy (via displacements) joins `mu` to
`mu' o res_F`, so they have the same class in `H^1(X_d) = [X_d, T]` coordinatewise, and
`res_F^*` is the inclusion `e_(f,j) -> f e_j`. QED.

**The model map.** Let `phi: K -> Q` be an LEF model with `K ⊇ W ∪ F ∪ WF`. Define
`tau_Q: (T^d)^Q -> (T^d)^Q` by `tau_Q(u)_q = mu'(p_q u)`, with
`(p_q u)(f) = u(q phi(f))` for `f in F`. It is continuous. Its `H^1` map is
`tau_Q^*(q e_i) = sum_(f,j) c_(i,f,j) q phi(f) e_j = q · (row i of phi(D))`,
where `phi(D)` applies `phi` to the entries (`supp D <= F <= K`). So, identifying
`H^1(T^(dQ)) = Z[Q]^d` by `e_(q,j) = q e_j`, `tau_Q^*(xi) = xi phi(D)`.

**Lemma C (small fibres).** Take `eps = 1/16` in Lemma A, giving `W, eta`, and
`eps_1 = eta/3` in Lemma B, giving `F, mu'`. For every LEF model with
`K ⊇ W ∪ F ∪ WF`, the fibres of `tau_Q` have sup-diameter `< 1/16`.

*Proof.* Let `tau_Q(u) = tau_Q(u')` and fix `q in Q`. Define `x in X_d` by
`x_k = u(q phi(k))` for `k in WF` and `x_k = 0` otherwise; define `y` from `u'` the same
way. For `w in W` and `f in F` we have `w, f, wf in K`, so
`(w^-1 x)_f = x_(wf) = u(q phi(wf)) = u(q phi(w) phi(f)) = (p_(q phi(w)) u)(f)`.
Hence
`rho(tau(x)_w, tau_Q(u)_(q phi(w))) = rho(mu(w^-1 x), mu'((w^-1 x)|_F)) < eta/3`,
and the same for `y, u'`. Since `tau_Q(u) = tau_Q(u')`,
`rho(tau(x)_w, tau(y)_w) < 2 eta / 3 < eta` for every `w in W`. By Lemma A,
`rho(x_1, y_1) < 1/16`. As `1 = 1·1 in WF` and `phi(1) = 1`, this reads
`rho(u(q), u'(q)) < 1/16`. The point `q` was arbitrary. QED.

**Theorem 2.** Let `G` be LEF and `tau` injective. Then:
1. For every LEF model with `K ⊇ W ∪ F ∪ WF`, `tau_Q` is onto and right multiplication by
   `phi(D)` is bijective on `Z[Q]^d`, so `phi(D) in GL_d(Z[Q])`.
2. `D` is a two-sided non-zero-divisor in `M_d(Q[G])`: `xi D = 0` or `D xi = 0` with
   `xi in Q[G]^d` (row, resp. column) forces `xi = 0`.
3. `tau` is onto, hence a homeomorphism of `X_d`.

*Proof.*
1. Lemma C and Theorem 1 with `N = d|Q|`. The `H^1` map is `xi -> xi phi(D)` (above), a
   bijective endomorphism of the free left `Z[Q]`-module `Z[Q]^d`, given by right
   multiplication. Its inverse is again left-linear, hence right multiplication by some
   `E`, and `phi(D) E = E phi(D) = I` (evaluate on the basis `e_i`).
2. Let `0 != xi in Z[G]^d` (clear denominators) with `xi D = 0`. Put `S = supp xi`, take
   `K ⊇ W ∪ F ∪ WF ∪ S ∪ SF` and an LEF model, and extend `phi` linearly to `Z[K]`.
   For `a in S`, `b in F` we have `phi(a) phi(b) = phi(ab)`, so expanding the products
   gives `phi(xi) phi(D) = phi(xi D) = 0`. Since `phi` is injective on `S`,
   `phi(xi) != 0`. This contradicts part 1. For a column `xi` with `D xi = 0` use `FS` in
   place of `SF`.
3. Part 2 gives that `xi -> xi D` is injective on `Q[G]^d`, and
   `torus-automata-with-regular-degree-are-surjective` (ESTABLISHED) gives `tau` onto.
   A continuous bijection of a compact Hausdorff space is a homeomorphism. QED.

*Remarks.*
- Only the LEF property at the finite sets `W ∪ F ∪ WF ∪ S ∪ SF` is used, where `W, F`
  depend on `tau`. Unlike the RPP result (`torus-degree-regular-on-prime-power-residual-support`),
  this does not reduce to the subgroup generated by `supp D`: `W` and `F` come from the
  global modulus of `tau^-1`.
- Part 3 also follows without C1. Given `y`, the models are onto, and compactness in
  `X_d` gives a preimage; the degree lemma is simply shorter to cite.
- Residually finite groups are recovered with `Q` a finite quotient, but the proof never
  uses an invariant finite-dimensional submanifold of `X_d`. The model map `tau_Q` is
  not a restriction of `tau`: it is not injective, and Theorem 1 replaces invariance of
  domain.

## 4. Hosts, and what changes on the graph

**Which groups are LEF.** Each item below has a short self-contained proof.
- *Locally finite groups.* A finite `K` lies in a finite subgroup `Q`; take `phi` the
  inclusion. This covers `Q/Z`, `Z(2^inf) x Z(3^inf)`, `Alt_fin(N)`, `FSym(N)` and
  every locally finite group.
- *Locally residually finite groups.* A finite `K` lies in a finitely generated
  subgroup `H`. If `H` is residually finite, a finite quotient `H -> Q` injective on
  `K` is an LEF model. This covers every abelian group, so the circle and torus cases
  of all abelian groups follow at every `d`. By Mal'cev's theorem (a finitely
  generated linear group is residually finite) it also covers every linear group.
- *`G = FSym(Z) ⋊ Z`.* Here `t` acts by `n -> n + 1`, permutations act on the left, and
  `t pi t^-1` has support `supp(pi) + 1`.
  - *Generation.* `G` is generated by `t` and `s = (0 1)`, since the conjugates
    `t^n s t^-n = (n, n+1)` generate `FSym(Z)`.
  - *Not residually finite.* `G` contains the infinite simple group `FAlt(Z)`. A
    residually finite group has only residually finite subgroups, and an infinite
    simple group has no nontrivial finite quotient.
  - *LEF.* Let `K` be finite. Every element of `K` is `sigma t^k` with
    `supp(sigma) ⊆ [-R, R]` and `|k| <= R`, for some `R`. Put `M = 4R + 2` and
    `I = [-2R, 2R]`, so `|I| < M`. For `pi` supported in `I`, let `pi-bar in Sym(Z/M)`
    act by `n mod M -> pi(n) mod M` for `n in I`, fixing the other residues. Then
    `pi -> pi-bar` is an injective homomorphism on permutations supported in `I`. Let
    `r` be the rotation `n -> n + 1` of `Z/M`. Then `r^k pi-bar r^-k` is the bar of
    `t^k pi t^-k` whenever both supports lie in `I`. Define
    `phi(sigma t^k) = sigma-bar r^k`.
    - *Multiplicativity.* Let `a = sigma t^k`, `b = pi t^l`, and `ab` all lie in `K`.
      Then `ab = (sigma · t^k pi t^-k) t^(k+l)`. The support of `t^k pi t^-k` is
      `supp(pi) + k ⊆ I`, and the permutation part of `ab` is supported in `[-R, R]`.
      So its bar is `sigma-bar r^k pi-bar r^-k`, and `phi(ab) = phi(a) phi(b)`.
    - *Injectivity.* Suppose `sigma-bar r^k = pi-bar r^l`. Then `r^(k-l)` fixes every
      residue outside the image of `[-R, R]`, and such residues exist because
      `M > 2R + 1`. Since `0 <= |k - l| <= 2R < M`, this forces `k = l`, and then
      `sigma = pi`.
  - So `FSym(Z) ⋊ Z` is a finitely generated LEF group that is not residually finite.
    It is torus-surjunctive at every `d` by Theorem 2, and no earlier graph result
    covered it. It is amenable, so this adds no new finite-alphabet case.

**Who is left: the new frontier.** A finitely presented LEF group is residually finite.
- *Proof.* Let `G = <S | R>` and `g != 1`. Choose a word for `g` and take `K` to contain
  every prefix of `g`'s word and of each relator, together with `S`. An LEF model
  `phi: K -> Q` extends to a homomorphism from the free group on `S`. By induction along
  prefixes it sends each relator to `phi(1) = 1`, and `g` to `phi(g) != 1`.
- *Consequence.* C2 and TS are now open only on non-LEF groups. The finitely presented
  non-residually-finite groups form the natural first class.
- *Two concrete hosts, both at `d = 2`.* Take `BS(2,3)` (non-Hopfian, hence not
  residually finite) or Thompson's `F` (its commutator subgroup is infinite simple, so
  `F` is not residually finite). Both are finitely presented, hence not LEF.
- *Why `d = 1` is covered there.* Both groups have a domain rational group ring:
  - `BS(2,3)` is a torsion-free one-relator group, hence locally indicable (Brodskii),
    and locally indicable groups satisfy the zero-divisor conjecture (Higman);
  - `F` is bi-orderable, so `Q[F]` embeds in a Malcev–Neumann division ring.
  So `d = 1` is covered by the domain case of
  `torus-automata-over-rf-or-domain-groups-are-surjunctive`. These standard facts
  select hosts only and are not used in any proof. The first open instances are
  therefore `d = 2` over `BS(2,3)` or `F`, together with every non-LEF group with
  torsion.

**Graph-level belief changes.**
- *The w9 conclusion is refuted.* "C2 and TS are open where GOT is trivial" does not
  hold. On `Z(2^inf) x Z(3^inf)` and `Q/Z`, Theorem 2 gives C2 at every `d`.
- *The w9 test is answered.* No injective `tau` over any LEF group has
  `D = s + s^2 - t`. That `D` is a zero divisor in `Z[Z/6]`, while Theorem 2(2)
  requires `D` to be a non-zero-divisor.
- *What the Bezout witness really obstructs.* It obstructs augmentation-only proofs,
  as w9 correctly records. It does not obstruct C2. Theorem 1 sees all of `phi(D)`,
  not just `epsilon(D)`.
- *What the w9 heuristic needed.* The `D` above has degree `0` on every finite block
  (it kills `(1-t)(1-s)`). Theorem 2 shows that an injective `tau` over `Z/6` forces
  `D` to be a unit in `Z[Z/6]`, so the "carry information between blocks" scenario
  cannot occur.
- *Relation to the RPP result.* The two are incomparable. RPP needs only
  `<supp D>` residually prime-power with `G` arbitrary. Theorem 2 needs `G` LEF, with
  no condition on `supp D`.

## 5. Theorem 3: no defect-tolerant small-fibre lemma

The obvious sofic extension would run the Section 3 construction on a sofic
approximation `sigma: G -> Sym(V)`. At good points `v` (where `sigma` is multiplicative
and locally injective on `WF`), the proof of Lemma C gives smallness of the fibres of
`tau_sigma` in the coordinates at `v`. At the few bad points there is no control. The
hoped-for statement would be:

> fibres small outside a set of `beta N` coordinates  =>  `rank f^* >= (1 - c beta) N`.

Combined with Elek–Szabó rank approximation on the degree side, this would give C2 for
sofic groups. It fails completely, already with one bad coordinate.

**Theorem 3.** For every `N >= 2` there is a continuous `f: T^N -> T^N` such that:
- `f(u) = f(v)` implies `u_i = v_i` for all `i <= N - 1`;
- `f^* = 0` on `H^1(T^N; Z)`;
- `f` is not onto.

*Proof.*
- *Embedding.* `T^(N-1)` embeds in `R^N`, by induction. `T^1` is the unit circle in
  `R^2`. Given an embedding `e: T^k -> R^(k+1)`, translate it so that its last coordinate
  is `> 0`. Then `(y, theta) -> (y_1, ..., y_k, y_(k+1) cos theta, y_(k+1) sin theta)` is
  a continuous injection `T^k x T -> R^(k+2)`, since `y_(k+1) > 0` recovers
  `y_(k+1)` and `theta`. A continuous injection from a compact space into a Hausdorff
  space is an embedding.
- *Construction.* Scale the embedding into a ball `B` of radius `1/8` in `R^N`. `B`
  maps injectively onto a ball in `T^N`, which gives an embedding `iota: T^(N-1) -> T^N`
  with image in a contractible ball. Put `f(u) = iota(u_1, ..., u_(N-1))`.
- *Properties.* Fibres are the circles `{u_1..u_(N-1) fixed}`. `f` factors through a
  contractible set, so `f^* = 0`, and its image is a proper compact subset. QED.

*What this kills.* It kills every attempt to prove C2 beyond LEF groups using only the
fibre-smallness profile of a finite model map. This includes the natural
sofic-with-defects version of Theorem 1 and any version with a rank bound in terms of
the number of bad coordinates.
- *Invariant.* The set of coordinates on which fibres are small.
- *Step.* Theorem 1's Step 2, which glues local inverses. It needs every coordinate of
  every ball to be controlled, and one uncontrolled coordinate lets the whole map
  collapse to a point in cohomology.

*What survives.*
- A sofic argument must use the fact that `tau_sigma` is local: each output coordinate
  depends only on a bounded neighbourhood.
- The defect must then be propagated through the sofic graph, for example by a
  mean-dimension or rank-counting argument that uses the Følner or sofic geometry, not
  just a fibre bound.
- The counterexample `f` is maximally nonlocal: its whole image depends on all
  coordinates at once.
- The natural next need is a local small-fibre lemma for sofic models. The expected
  form: fibres small at a `(1 - beta)`-fraction of vertices, with memory `F`, imply
  `rank f^* >= (1 - C(F) beta) N`.
