# Kazhdan subgroups of nV: displacement gap, Kazhdan projections, bounded slopes (2026-09-17)

Lane c-kaznv (wave swarm-0917), role transplanter, family operator-algebras.
Target hole: `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`.
Notation as in `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`
(bricks, canonical charts, depth `D_g`, slope cocycle `s(g,x) ∈ Z^n` with
`s(gh,x) = s(g,hx) + s(h,x)`, the open invariant set `U_K`, `Z_K = C^n \ U_K`).

Summary.
- **A (zero-one law).** For a Kazhdan pair `(Q, ε)` of a countable group `K` acting on a
  compact metrizable `Z`, the displacement `D_Q(ν) = max_{q∈Q} ||q_*ν - ν||_1` has
  `min_{Prob(Z)} D_Q ∈ {0} ∪ [ε², 2]`. For an infinite Kazhdan `K <= nV` it is `>= ε²`
  on `Prob(Z_K)`. Every "vanishing error" construction is equivalent to one measure with
  displacement below `ε²`, and pushforwards of Følner windows of invariant σ-finite
  measures on `K`-covers of `Z` are such constructions, so they are all equivalent to the
  target on `Z`.
- **B (Kazhdan projection transplant).** The image of the Kazhdan projection in the
  reduced germ-groupoid algebra `C*_r(G_K|Z)` is nonzero iff `Z ∩ U_K ≠ ∅`, and in the
  maximal algebra iff `Z` carries an invariant probability measure. The target on an
  infinite minimal set lives in the kernel of `C*(G_K|Z) -> C*_r(G_K|Z)`.
- **C (Gottschalk–Hedlund for slopes).** For finitely generated `K <= nV` (no (T)) and
  a minimal closed `K`-invariant `Z`: if `sup_{g∈K} |s(g,x)| < ∞` at one `x ∈ Z`, then
  `Z ⊆ U_K`, so `Z` is a finite orbit.
- **D (fibration stabilizers).** Kazhdan subgroups of the stabilizer in `nV` of a
  coordinate fibration `C^n -> C^I` are finite.

Imports (standard, not re-read at source): defining form of (T) with a Kazhdan pair
(BdlHV Definition 1.1.3); countable Kazhdan groups are finitely generated and
finite-index subgroups and quotients of Kazhdan groups are Kazhdan (BdlHV Theorem 1.3.1,
Theorem 1.7.1, Theorem 1.3.4); the Kazhdan projection `p_K ∈ C*_max(K)` exists and every
unitary representation `σ` sends it to the projection onto `σ`-invariant vectors (Akemann–
Walter; Valette); Farley, Thompson's group V is a-T-menable
(`thompson-v-has-haagerup-property`), so Kazhdan subgroups of V are finite.

## A. The displacement zero-one law

**Lemma A1.** Let `K` be countable with Kazhdan pair `(Q, ε)`, acting by homeomorphisms on
a compact metrizable `Z`. If some `ν ∈ Prob(Z)` has `||q_*ν - ν||_1 < ε²` for all
`q ∈ Q`, then `Z` carries a `K`-invariant probability measure `μ`, and `μ << ν̄` for
`ν̄ = Σ_{g∈K} c_g g_*ν` (any weights `c_g > 0` with sum 1).

*Proof.*
- `ν̄` is `K`-quasi-invariant, and `ν`, `g_*ν << ν̄`.
- `π(g)f(x) = f(g^{-1}x) (d g_*ν̄ / dν̄)(x)^{1/2}` is a unitary representation on
  `L²(Z, ν̄)`.
- `ξ = (dν/dν̄)^{1/2}` is a unit vector and `π(g)ξ = (d g_*ν / dν̄)^{1/2}`.
- With `(√a - √b)² <= |√a - √b|(√a + √b) = |a - b|`:
  `||π(q)ξ - ξ||² <= ∫ |d q_*ν/dν̄ - dν/dν̄| dν̄ = ||q_*ν - ν||_1 < ε²`.
- By the Kazhdan pair there is `η ≠ 0` with `π(g)η = η` for all `g`. Then
  `g_*(|η|²ν̄)(A) = ∫_A |η∘g^{-1}|² (d g_*ν̄/dν̄) dν̄ = ∫_A |π(g)η|² dν̄ = ∫_A |η|² dν̄`, so
  `μ = |η|²ν̄ / ||η||²` is invariant and `μ << ν̄`. ∎

**Lemma A2 (lower semicontinuity).** `D_Q` is weak-* lower semicontinuous on `Prob(Z)`,
so it attains its minimum.

*Proof.* `||q_*ν - ν||_1 = sup { |∫ (f∘q - f) dν| : f ∈ C(Z), |f| <= 1 }` (Riesz), a
supremum of weak-* continuous functions of `ν`; a finite maximum of lsc functions is
lsc; `Prob(Z)` is weak-* compact. ∎

**Theorem A3 (zero-one law).** `m_Q(Z) := min_{ν∈Prob(Z)} D_Q(ν)` is `0` if `Z` carries an
invariant probability measure and is `>= ε²` otherwise.

**Corollary A4.** Let `K <= nV` be an infinite Kazhdan subgroup with Kazhdan pair `(Q,ε)`.
Then `Z_K ≠ ∅` and every `ν ∈ Prob(Z_K)` has `max_q ||q_*ν - ν||_1 >= ε²`.
*Proof.* Theorem 3 and Corollary 4 of the criterion artifact: `Z_K` is nonempty closed
invariant with no invariant probability measure. Apply A3 to `Z_K`. ∎

**Corollary A5 (target, quantitatively).** The target is equivalent to: for every Kazhdan
`K <= nV` with Kazhdan pair `(Q,ε)` and every minimal closed invariant `Z`, some
`ν ∈ Prob(Z)` has `||q_*ν - ν||_1 < ε²` for all `q ∈ Q`. (⇐ A1; ⇒ take `ν` invariant.)

**Corollary A6 (windows project).** Let `Y` be a standard Borel `K`-space with a
`K`-invariant σ-finite measure `λ` and a Borel `K`-equivariant `p: Y -> Z`. If a Borel
`W ⊆ Y` has `0 < λ(W) < ∞` and `λ(qW Δ W) < ε² λ(W)` for all `q ∈ Q`, then `Z` carries
an invariant probability measure.
*Proof.* `ν = p_*(λ|_W)/λ(W)`. By invariance of `λ` and equivariance,
`q_*ν = p_*(λ|_{qW})/λ(W)`, and pushforward does not increase `||·||_1`, so
`||q_*ν - ν||_1 <= λ(qW Δ W)/λ(W) < ε²`. Apply A1. ∎

**Corollary A7 (finite windows on infinite orbits).** If every `K`-orbit in `Z` is
infinite, then every finitely supported `ν ∈ Prob(Z)` has `D_Q(ν) >= ε²`; in particular
for every finite `F` inside a union of infinite orbits, `max_q |qF Δ F| >= ε²|F|`.
*Proof.* If `D_Q(ν) < ε²`, A1 gives an invariant `μ << ν̄`, and `ν̄` is carried by the
countable set `K·supp ν`. An invariant probability measure on a countable set has an atom
of maximal mass, and the set of atoms of that mass is finite and invariant: a finite
orbit. ∎ (For a single orbit this is the spectral-gap corollary already recorded in
`finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite`.)

**What A kills.**
- *Vanishing-error limits carry nothing.* Any argument producing `ν_k ∈ Prob(Z)` with
  `D_Q(ν_k) -> 0` (brick transport with shrinking bad sets, Følner windows, random walk
  averages) is equivalent to producing one `ν` with `D_Q(ν) < ε²`, which by A1 is
  equivalent to the target on `Z`. The invariant is `m_Q(Z)`; in a counterexample it is
  `>= ε²` on `Z_K`, so the threshold cannot be reached by error terms, only by an exact
  mechanism.
- *Skew products and covers.* By A6, an invariant σ-finite `λ` with a `Q`-Følner window
  on any `K`-cover of `Z` (an orbit `Kx` with counting measure; the skew product
  `Kx x Z^n` with `g(y,ℓ) = (gy, ℓ + s(g,y))` and counting measure; any skew product
  over a `K`-quasi-invariant measure on `Z` with a cocycle-twisted invariant measure, as in
  Section 6 of the criterion artifact) already gives the target on `Z`. The step where
  each such approach dies is the window: on the counting-measure covers every finite
  window lies over finitely many points of `Z` and A7 forbids it when the orbits are
  infinite; on diffuse covers the window's pushforward is an almost invariant `ν` with
  `D_Q(ν) < ε²`, so constructing the window is the target.
- *Where (T) can still enter.* Only through the fixed threshold `ε²` on a single measure,
  or through an exact invariant object. A proof must use a nV-specific mechanism that
  produces displacement `< ε²` in one step.

## B. Kazhdan projections in germ-groupoid algebras

Let `K <= nV` have (T) and let `Z` be closed and `K`-invariant. Let `G_K|Z` be the
groupoid of germs `[g, x]` of elements `g ∈ K` at points `x ∈ Z`, where germs are taken
in `C^n` (two elements have the same germ at `x` if they agree on a neighbourhood of `x`
in `C^n`). To avoid non-Hausdorff groupoid-algebra technicalities, work with covariant
representations directly.
- A **germ representation** of `Z` is a pair `(π, u)`: a representation `π` of `C(Z)` and
  a unitary representation `u` of `K` on the same space with `u_g π(f) u_g^* = π(f∘g^{-1})`
  and `u_g π(1_{E∩Z}) = π(1_{E∩Z})` whenever `g` is the identity on a clopen `E ⊆ C^n`.
  `C*(G_K|Z)` denotes the universal C*-algebra of germ representations (a quotient of
  `C(Z) ⋊_max K`).
- For `x ∈ Z` let `(G_K|Z)_x` be the set of germs with source `x`, and `ρ_x` the germ
  representation on `l²((G_K|Z)_x)` with `ρ_x(f)δ_γ = f(r(γ))δ_γ` and
  `ρ_x(u_g)δ_γ = δ_{[g, r(γ)]γ}`. The germ relation holds: if `g = id` on `E ∋ r(γ)` then
  `[g, r(γ)]` is a unit. `C*_r(G_K|Z)` denotes the image of `C*(G_K|Z)` in
  `B(⊕_x l²((G_K|Z)_x))`.
- Let `a_max`, `a_r` be the images of `p_K` under `C*_max(K) -> C*(G_K|Z) -> C*_r(G_K|Z)`.

**Proposition B1.** `a_r ≠ 0` iff `Z ∩ U_K ≠ ∅`.
*Proof.*
- `a_r ≠ 0` iff some `ρ_x(a_r) ≠ 0`. `ρ_x(u_g)` is a permutation of the basis, and
  `ρ_x(a_r)` is the projection onto
  `K`-invariant vectors of this permutation representation, which is nonzero iff `K`
  has a finite orbit on `(G_K|Z)_x`.
- The orbit of `γ` with `r(γ) = y` is in bijection with `{[g,y] : g ∈ K}`. So `a_r ≠ 0`
  iff some `y ∈ Z` has finitely many germs of `K` at `y`.
- Finitely many germs at `y` ⇒ finite orbit (the germ determines `gy`), finite-index
  stabilizer `K_y`, finite germ group at `y`, so the elements with trivial germ at `y`
  form a finite-index subgroup `K_0`. `K_0` is finitely generated (finite index in a
  Kazhdan group); its generators are the identity on a common clopen neighbourhood `E`
  of `y`, hence so is `K_0`; so `y ∈ U_K`. Conversely `y ∈ U_K` gives a finite-index
  subgroup with trivial germs at `y`, hence finitely many germs. ∎

**Proposition B2.** `a_max ≠ 0` iff `Z` carries a `K`-invariant probability measure.
*Proof.* If `μ` is invariant, the Koopman pair on `L²(Z, μ)` (`π(f)` multiplication,
`u_g ξ = ξ∘g^{-1}`) is a germ representation (if `g = id` on `E`, then
`u_g(1_E ξ) = 1_E ξ`), and `u_g 1 = 1`, so `a_max` acts as a projection with `1` in its
range. Conversely if `σ(a_max) ξ = ξ ≠ 0`
for a representation `σ`, then `ω(f) = ⟨σ(f)ξ, ξ⟩/||ξ||²` on `C(Z) ⊆ C*(G_K|Z)` satisfies
`ω(f∘g^{-1}) = ⟨σ(u_g) σ(f) σ(u_g)^* ξ, ξ⟩ = ω(f)`, an invariant state, i.e. an invariant
probability measure. ∎

**What B kills.** For a Kazhdan `K` and a minimal `Z`, `Z ∩ U_K ≠ ∅` forces `Z ⊆ U_K`,
and then `Z` is a finite orbit. So on an infinite minimal `Z`, `a_r = 0` always, and the
target on `Z` is `a_max ≠ 0`, a statement about the kernel of `C*(G_K|Z) -> C*_r(G_K|Z)`.
Every transplant that certifies nonvanishing by reduced-norm data (regular or
quasi-regular representations on orbits, ghost-projection approximations, Roe-algebra or
coarse estimates on Schreier graphs, reduced `K`-theory, the conditional expectation onto
`C(Z)`) sees `0` and dies at that quotient. A nonzero `a_max` needs a non-regular
representation with invariant vectors, and B2 says this is an invariant measure: the
transplant is circular. Amenability of the Brin–Thompson groupoid is not used and would
not help directly, because `G_K|Z` is the germ groupoid of `K` on a `K`-invariant set,
not a restriction of the nV-groupoid to an nV-invariant set.

## C. Gottschalk–Hedlund for the slope cocycle

**Theorem C1.** Let `K <= nV` be finitely generated and `Z ⊆ C^n` a minimal closed
`K`-invariant set. If `sup_{g∈K} |s(g,x)|_∞ < ∞` for one `x ∈ Z`, then `Z ⊆ U_K`, and `Z`
is a finite orbit.

*Proof.*
- **Skew product.** `K` acts on `Z x Z^n` by `g(y,m) = (gy, m + s(g,y))`; this is an
  action by the cocycle identity, and it commutes with the translations
  `τ_t(y,m) = (y, m+t)`.
- **Compact minimal set.** The orbit of `(x,0)` lies in `Z x [-B,B]^n`, so its closure
  is compact and contains a minimal closed invariant `M`. Its projection to `Z` is closed,
  nonempty and invariant, hence equal to `Z`.
- **M is a graph.** If `(y,m), (y,m+t) ∈ M` with `t ≠ 0`, then `M` and `τ_t M` are minimal
  and meet at `(y, m+t)`, so their intersection, a nonempty closed invariant subset of
  both, equals both: `τ_t M = M`, so `τ_{kt} M = M` for all `k`, contradicting
  compactness. So `M` is the graph of `φ: Z -> Z^n` with `φ(gy) = φ(y) + s(g,y)`. A closed
  graph with compact range makes `φ` continuous, hence locally constant with finitely
  many values.
- **Potential and bricks.** Put `F = -φ`, so `s(g,y) = F(y) - F(gy)` on `Z`. Choose `c0`
  such that `F` is constant on `Z ∩ B` for every brick `B` of shape `>= c0·1` (compactness
  of `Z`, local constancy). Let `S` be a finite symmetric generating set and choose
  `c` with `c·1 + F(y) >= max(c0, max_{h∈S} D_h)·1` for all `y ∈ Z`. For `y ∈ Z` let
  `B(y)` be the brick of shape `c·1 + F(y)` containing `y`.
- **Finite canonically permuted family.** There are finitely many shapes, so
  `P = {B(y) : y ∈ Z}` is finite. If `z ∈ Z ∩ B(y)` then `F(z) = F(y)` and `B(z) = B(y)`,
  so distinct members of `P` meet `Z` in disjoint sets. For `h ∈ S`, `h` is canonical on
  `B(y)` (depth), and `hB(y)` is the brick of shape `c·1 + F(y) - s(h,y) = c·1 + F(hy)`
  containing `hy`, i.e. `B(hy)`. Canonical maps compose, so every `g ∈ K` maps `B(y)`
  canonically onto `B(gy)`.
- **Conclusion.** `K` permutes the finite set `P`; the kernel `K_0` of this permutation
  action has finite index and each `g ∈ K_0` satisfies `g∘φ_B = φ_B` on each `B ∈ P`,
  so `g` is the identity on `∪P ⊇ Z`, an open set. So `Z ⊆ U_K`. A point of `U_K` has a
  finite orbit (it is fixed by a finite-index subgroup), and a minimal set containing a
  finite orbit is that orbit. ∎

**Corollary C2.** In a minimal closed invariant set of a finitely generated `K <= nV`
that is not a finite orbit, the slope cocycle is unbounded along every orbit. In
particular this holds on every minimal subset of `Z_K`.
*Proof.* A minimal set that meets `U_K` is contained in it (open invariant set) and is a
finite orbit; apply C1 to the others. ∎

**Relation to the graph.** `finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite`
shows (Steps 0-6, audited sound) that a finitely generated `K` is finite iff the slope is
bounded at every point of `C^n`. C1 is local and uses one point: bounded slope at a single
point of a minimal set pins that whole minimal set in `U_K`, through minimality of the
skew product rather than brick induction over words.

**What C kills.** Constructions of a potential or height on a minimal `Z ⊆ Z_K` that
are bounded on an orbit (bounded-height brick selections, continuous or bounded
measurable-on-orbits heights, Busemann heights with bounded range) cannot exist. Any
potential for the slope cocycle on such `Z` is unbounded on every orbit, so the
measurable potential of the criterion's Lemma 1 must have infinite range, and any
invariant measure has to see arbitrarily deep bricks.

## D. Stabilizers of coordinate fibrations

For `I ⊊ {1,...,n}` nonempty with complement `J`, let `Stab_I <= nV` be the elements that
map every fibre `{a} x C^J` onto a fibre: `g({a} x C^J) = {v(a)} x C^J` for a bijection
`v` of `C^I`. So `g(x_I, x_J) = (v(x_I), φ_{x_I}(x_J))` with each `φ_a` a bijection.
(Requiring only that the output `I`-coordinates depend on `x_I` is weaker and not a
subgroup statement we use: `(0u, y) -> (u, 0y)`, `(1u, y) -> (u, 1y)` in `2V` has
non-injective `v`.)

**Proposition D1.** Every Kazhdan subgroup `K` of `Stab_I`, and of any conjugate
`h Stab_I h^{-1}` with `h ∈ nV`, is finite.
*Proof (induction on n; n = 1 is Farley's theorem).*
- `g -> v` is a homomorphism `Stab_I -> |I|V`: `v` is a bijection of `C^I`, and on each
  piece `[w_I] x [w_J] -> [w'_I] x [w'_J]` of a brick partition for `g` it is the prefix
  replacement `w_I -> w'_I`, so `v` is piecewise canonical on the finite partition of
  `C^I` by bricks of shape `D_g·1`. The image of `K` is a Kazhdan subgroup of
  `|I|V`, finite by induction since `|I| < n`; its kernel `K_1` has finite index and is
  Kazhdan.
- An element of the kernel is `(x_I, x_J) -> (x_I, φ_{x_I}(x_J))`. On a piece
  `[w_I] x [w_J] -> [w'_I] x [w'_J]` the `I`-part is the identity, so `w'_I = w_I`, and
  `φ_a` acts on `[w_J]` by `w_J -> w'_J` for every `a ∈ [w_I]`. Hence `φ_a ∈ |J|V` and
  `a -> φ_a` is constant on bricks of shape `D_g·1` in `C^I`. `K_1` is finitely generated, so there is a finite
  partition `P` of `C^I` into bricks on which each generator's `φ` is constant; the maps
  constant on `P` form a subgroup, so `K_1 <= Π_{B∈P} |J|V`.
- Each coordinate projection of `K_1` is a Kazhdan subgroup of `|J|V`, finite by induction;
  `K_1` embeds in the finite product of these images, so it is finite, and so is `K`.
- Conjugation by `h ∈ nV` preserves (T) and finiteness. ∎

**What D gives.** An infinite Kazhdan subgroup of `nV` virtually preserves no
`nV`-image of a coordinate fibration. A decomposition "every Kazhdan `K <= nV` virtually
lies in a conjugate of some `Stab_I`" would finish the flagship hole; its prerequisite can
fail independently of the target (no argument is known that (T) forces a preserved
fibration), so it is recorded only as a candidate prerequisite, not as a route.

## E. Honest status

None of A-D proves the target. A and B are exact reformulations that convert two families
of approaches (vanishing-error transport, Kazhdan-projection transplant through reduced
algebras) into the target itself and name the invariant where they die (`m_Q(Z) >= ε²` on
`Z_K`; the kernel of `C*(G_K|Z) -> C*_r(G_K|Z)`). C and D are unconditional constraints on
a counterexample: unbounded slopes along every orbit of every infinite minimal set, and no
virtually preserved coordinate fibration.
