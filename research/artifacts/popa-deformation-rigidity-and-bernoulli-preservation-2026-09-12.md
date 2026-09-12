# Popa deformation/rigidity cannot force injective automata to preserve Bernoulli measure

Lane `gk-p-bernoulli-popa`, 2026-09-12. Supports the Cairn claim
`deformation-rigidity-gives-no-coordinate-level-bernoulli-input`.

The question: over a group with property (T), or with an infinite normal
subgroup with relative property (T), can Popa's cocycle superrigidity or his
deformation/rigidity theory force an injective cellular automaton
`tau: A^G -> A^G` to satisfy `tau_* mu = mu`? Here `mu` is the uniform product
measure. By `injective-measure-preserving-ca-is-surjective` that would make
`tau` surjective. With `gottschalk-reduces-to-fg-simple-kazhdan-groups` it would
decide the conjecture positively.

The answer recorded here is no. Each tool of the theory either holds on a
shift that carries a strict embedding, or has a conjugacy-invariant conclusion,
or acts only on measures that a strict image avoids. Sections 1–4 give the four
reasons; Section 5 states what a working proof must supply instead.

The general fact that measure-conjugacy invariants agree on `mu` and
`tau_* mu` is recorded by the sibling lane `gk-p-bernoulli-ergodic`
(`measure-conjugacy-invariants-cannot-certify-surjectivity`). This artifact is
only about what is specific to Popa's theory.

## 0. Setting and the singularity of strict images

Let `G` be a group, `A` a finite alphabet with `|A| >= 2`, `X = A^G`, `mu` the
uniform product measure, `tau` an injective cellular automaton, `Y = tau(X)`
and `nu = tau_* mu`.

**Lemma 0.1.** If `tau` is not surjective, then `nu` is singular to `mu`, and
every joining of `nu` with any measure is singular to the corresponding product
with `mu`.

*Proof.* `Y` is closed and misses a pattern `p` on a finite window `Omega`.
Choose infinitely many pairwise disjoint translates `g_i Omega`. The events
"`x` shows `p` at `g_i Omega`" are independent under `mu`, and each has
probability `|A|^-|Omega| > 0`. By Borel–Cantelli, `mu`-almost every `x` shows `p`
somewhere, so `mu(Y) = 0` while `nu(Y) = 1`. A joining `lambda` of `nu` with any
`m` has marginal `nu`. If `lambda << mu x m`, its marginal would satisfy
`nu << mu`, which is false. QED

## 1. The malleable deformation never sees a strict image

Popa's s-malleable deformation of a Bernoulli shift, as quoted in
`research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md`
(Addendum 21, arXiv:math/0512646, abstract level, e.g. `Gamma` acting on
`[0,1]^Gamma`), is a continuous one-parameter group `alpha_t` of automorphisms of
`(X x X, mu x mu)`. It commutes with the diagonal action, and `alpha_1` carries
`L^infty(X) (x) 1` onto `1 (x) L^infty(X)`.

It is a transformation of the measure algebra of `mu x mu`, so it acts only on
`L^2(mu x mu)` and on the measures absolutely continuous with respect to
`mu x mu`. By Lemma 0.1:
* the image measure `nu` of a strict automaton is singular to `mu`;
* the graph joining `(id x tau)_* mu`, the natural object linking `mu` to `nu`,
  is singular to `mu x mu`.

So the product-coordinate deformation, which is the only coordinate-level
ingredient of the theory, is undefined on every measure that records the
window laws of `nu`.

Transporting the deformation through `tau` gives
`(tau x tau) alpha_t (tau x tau)^-1` on `(X x X, nu x nu)`. It is conjugate to the
original, so every statement it produces about `nu` is a conjugacy invariant
and therefore agrees with the statement for `mu`. The transported deformation
no longer rotates the coordinates of `A^G`, and it says nothing about cylinder
masses such as `nu([p]) = 0`.

**Conclusion 1.** Deformation/rigidity yields no inequality between cylinder
masses of `mu` and `nu`. Such an inequality is exactly what
`every-injective-ca-preserves-uniform-bernoulli-measure` needs: the window
balance identity.

## 2. The rigidity hypotheses hold on a shift with a strict embedding

`compressed-coset-shifts-carry-strict-equivariant-embeddings` gives a Kazhdan
calibration. Its data:
* `G = R^x` with `R = L_(F_2)(1,2)`: simple, with property (T);
* `H = V_1 <= G`, of infinite index;
* `u` with `u H u^-1 = V_11`, a proper subgroup of `H`;
* `psi(gH) = g u^-1 H`.

For every base space `X_0` with at least two points, `y -> y o psi` is a
continuous, equivariant, injective, non-surjective self-map of
`X_0^(G/H)`. Its image consists of the configurations constant on the fibres
of `psi`, which is a null set for the product measure.

Now take the diffuse base `X_0 = [0,1]` with Lebesgue measure, as in Popa's
example. The generalized Bernoulli action `G ↷ ([0,1]^(G/H), Leb^(G/H))` has
both hypotheses of the quoted cocycle superrigidity theorem:

* **s-malleable.** The deformation rotates each coordinate of
  `[0,1] x [0,1] = (circle x circle, Haar)` identically at every index. This
  commutes with any permutation of the index set, so the construction does not
  use the index set being `G` rather than `G/H`.
* **Weakly mixing on the Kazhdan subgroup.** Take `H' = G`, normal in itself,
  with property (T), hence w-rigid. A generalized Bernoulli action is weakly
  mixing exactly when every orbit on the index set is infinite. `G/H` is a
  single infinite orbit.

**Conclusion 2.** Consider any argument whose inputs are s-malleability of a
product shift over a `G`-set, together with weak mixing on a normal subgroup
with relative property (T). Popa's cocycle superrigidity, and everything
derived from it without further input, are examples. No such argument can
conclude that continuous equivariant injections of the product shift preserve
the product measure: the coset shift above refutes the conclusion.

`kazhdan-bernoulli-rigidity-forces-surjective-embeddings` already lists
spectral gap, strong ergodicity, Glasner–Weiss closedness and the absence of
finite quotients as properties this shift has. This section adds
s-malleability and the cocycle superrigidity hypotheses to that list.

What the calibration does not have is freeness of the action on the index
set. In Popa's theory freeness enters only through the orbit-equivalence and
W*-superrigidity corollaries. Their conclusions (orbit equivalence implies
conjugacy, algebra isomorphism implies conjugacy) are conjugacy invariants,
and the strict image action `G ↷ (X, nu)` is conjugate to the Bernoulli action
through `tau`. So the part of the theory that uses freeness proves nothing about
`nu` versus `mu`.

## 3. Rigidity of measure-preserving factor maps fails

A natural hope: a decoder `sigma` with `sigma o tau = id` could be upgraded by
rigidity from "measure preserving" to "injective". Measure-preserving self-maps
with finite memory are not rigid in that sense.

**Proposition 3.1.** Let `G` be a group with an element `s` of infinite order,
`A = Z/2`, and `xi(x)(g) = x(g) + x(g s)`. Then:
* `xi` is a cellular automaton with `xi_* mu = mu`;
* `xi` is not injective: its kernel is the set of configurations constant on
  every coset `g<s>`.

*Proof.* For a finite window `F`, `xi(x)|_F` is the image of `x|_(F union F s)`
under the incidence map of the edges `{g, gs}`, `g in F`. Inside each coset
`g<s>`, which is a copy of `Z` because `s` has infinite order, these edges form
disjoint unit segments. So the edge set is a forest. The incidence vectors of a
forest's edges are linearly independent over `F_2`, so the linear map
`F_2^(F union F s) -> F_2^F` is onto and pushes the uniform measure to the
uniform measure. `x(g) = x(gs)` for every `g` exactly when `x` is constant on
each coset `g<s>`. QED

Over `Z` this is `xor-lift-of-bernoulli-has-positive-fiber-entropy`. The point
here is that it runs over every group with an infinite-order element: `R^x`,
which contains Thompson's `V`, and every simple Kazhdan host with such an
element. So no rigidity statement about factor maps of Bernoulli shifts of
Kazhdan groups can say "measure preserving with finite memory implies
invertible".

## 4. Superrigidity on finite-fibre lifts yields only sections strict pairs already have

*Remark only. The Cairn nodes for finite extensions and flip lifts belong to the
sibling lane `gk-p-inf-kazhdan` (`kazhdan-map-bernoulli-finite-extensions-are-trivial`,
`strict-pair-flip-lifts-are-relatively-weakly-mixing`, and the citation claim
`popa-bernoulli-cocycle-superrigidity`). This section is not a prerequisite of
the claim this artifact supports.*

The one place a cocycle naturally appears is a lift of `mu` along a decoder.
Let `lambda` be an invariant measure on `X` with `sigma_* lambda = mu`. Suppose
its conditional measures on the fibres of `sigma` are uniform on `k` atoms,
almost surely.

By the Rokhlin skew-product theorem, `(X, lambda) -> (X, mu)` is isomorphic to
`X x {1,...,k}` with a measurable cocycle `c: G x X -> Sym(k)`. `Sym(k)` is
finite, hence in Popa's class `U_fin`. Assume the quoted theorem applies to
the Bernoulli shift over `A` (the trust surface is below). Then `c` is
cohomologous to a homomorphism `G -> Sym(k)`. That homomorphism is trivial
when `G` is infinite and simple. So `lambda` splits as `k` invariant measurable
sections of `sigma`.

Every strict pair already has such sections: `tau` itself, and infinitely many
cellular sections (`strict-split-decoders-have-infinitely-many-sections`). So a
successful application gives nothing new.

For the lifts that carry positive fibre entropy
(`strict-split-pairs-carry-positive-entropy-flip-lifts`), the conditional
measures are diffuse. The fibre cocycle then takes values in the automorphism
group of a diffuse probability space, which is not among the targets the quoted
theorem covers.

## 5. What a proof would have to supply

A positive proof on simple Kazhdan hosts must produce an inequality or identity
between cylinder masses, such as the window balance
`#{q in A^(Omega M) : tau(q)|_Omega = p} = |A|^(|Omega M| - |Omega|)`. It must use:
* locality of `tau` over the free regular index set `G`, since Section 2 shows
  non-free index sets admit strict embeddings with every rigidity hypothesis in
  place;
* coordinates, since Section 1 shows conjugacy-transported tools lose them;
* more than measure preservation of decoders, by Section 3.

Popa's theory produces none of these: its outputs are cohomology classes,
conjugacy statements, and uniform L^2-convergence of a deformation defined
only for measures absolutely continuous to the product measure.

Entropy combines a conjugacy invariant with a coordinate-level upper bound
(`strict-automaton-lowers-bernoulli-rokhlin-entropy`). A lower bound matching
that shape is `bernoulli-rokhlin-entropy-maximal-on-fg-simple-kazhdan-groups`,
and the lanes `gk-p-inf-*` own it.

## 6. Trust surface

* **Popa's cocycle superrigidity theorem**, quoted at abstract level in the
  km-lattice artifact, Addendum 21. The quote states s-malleability and weak
  mixing on a normal subgroup with relative property (T), with targets in
  closed subgroups of unitary groups of finite von Neumann algebras. No
  full-text theorem-number check has been done.
* **Section 2 needs only the definitions** of s-malleability and weak mixing,
  and both are checked above. The conclusion that the coset shift satisfies the
  theorem's hypotheses does not use the theorem's truth.
* **Section 4 does apply the theorem.** It also assumes the theorem covers
  Bernoulli shifts with a finite atomic base, which the abstract quote does not
  state. Section 4 is a remark: even a successful application gives nothing.
  No landed claim depends on it.
