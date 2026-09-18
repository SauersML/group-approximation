---
rg: 2
id: strict-pair-linear-shadows-exist-over-z
kind: claim
title: The linear shadow of a strict pair on local observables exists over every group with an element of infinite order, so linearization proofs of surjunctivity must use multiplicativity of the pullback
distinct_from:
  finite-pattern-orbit-closure-forces-surjunctivity: that proves surjectivity when the multiplicative pullbacks preserve a finitely generated observable module containing the one-site observables; this shows that the same module data without multiplicativity is realized over Z, and locates the use of multiplicativity at the extension from one-site observables to all of O.
  shift-homology-in-positive-degree-is-inert-under-automata: that shows positive-degree homology of the pattern permutation module sees only constants; this concerns the endomorphism monoid of the module itself in degree 0, where direct finiteness fails for finite-propagation maps.
  stable-finiteness-reduces-to-prime-field: that gives stable finiteness of Q[G] for every group; this shows it cannot be transferred to the observable module O, which is an infinite direct sum of finitely generated projectives.
  quantum-surjunctivity-conjecture: that keeps multiplicativity (unital *-endomorphisms of the quasi-local algebra); this drops it and shows the relaxed statement is false over Z.
  gottschalk-surjunctivity-conjecture: that is the goal; this is an obstruction to one class of proofs of it and a reformulation of it as direct finiteness of a monoid of algebra endomorphisms.
---

**ESTABLISHED** by `strict-pair-linear-shadows-over-z-proof`. The proof is self-contained apart from the
existence of local decoders for injective automata, which is proved in full in
`finite-pattern-projective-decoder-proof` (section "Every injective full-shift automaton has a local decoder").

**Setting.** `G` is a group, `A` a finite alphabet with `|A| = k >= 2`, `K` a field, and `O` the `K`-algebra of
functions `A^G -> K` that depend on finitely many coordinates. `G` acts by `(g.f)(x) = f(g^{-1} x)`. For `f` in `O`,
`D(f)` is the finite set of coordinates on which `f` depends. A `K`-linear map `L : O -> O` has *finite propagation*
if there is a finite `U ⊆ G` with `D(Lf) ⊆ D(f) U` for all `f`. The pullback `τ^* f = f ∘ τ` of a cellular automaton
with memory `N` has finite propagation with `U = N`.

**Theorem.**

**(A) The linear shadow exists.** Suppose `G` has an element `t` of infinite order, for example `G = Z`. Then there
are `K[G]`-linear maps `L, R : O -> O` with all of the following properties:
1. `R L = id` and `L R != id`, so `L` is not surjective and `R` is not injective;
2. `L 1 = R 1 = 1`, and `L`, `R` are the identity on every one-site observable;
3. finite propagation, with `D(Lf) ⊆ D(f){1,t}` and `D(Rf) ⊆ D(f){1,t^{-1}}`;
4. they preserve the degree (support size) of every tensor-basis monomial, and send basis monomials to basis
   monomials or to `0`, so they are defined over `Z` and preserve the monomial lattice;
5. they preserve the uniform Bernoulli integral `f -> ∫ f dμ`;
6. for `K = R` or `C`, `L` extends to a `G`-equivariant isometry of `L^2(A^G, μ)` that is not unitary, with
   `L^* = R`.

**(B) Strictness is exactly non-injectivity of a surjective algebra endomorphism.** For every group `G` and every
cellular automaton `τ` on `A^G`, with `T = τ^*`:
1. `T` has a `K`-linear right inverse iff `τ` is injective, and then `σ^*` is a finite-propagation `K[G]`-linear
   right inverse for any decoder `σ`;
2. `T` is injective iff `τ` is surjective. So for injective `τ`, every right inverse `S` has `S T != id` iff `τ` is
   not surjective.
3. The unital `G`-equivariant `K`-algebra endomorphisms of `O` are exactly the pullbacks of cellular automata.
   Hence `G` is surjunctive over `A` iff every surjective one of them is injective. This is direct finiteness of the
   monoid of equivariant unital algebra endomorphisms of `O`.

**The class this kills.** It kills every proof of surjunctivity, for a group containing an element of infinite order
(for instance any group containing `Z`), that uses the pair `(τ^*, σ^*)` only through properties that `(L, R)` also
has:
- `K[G]`-linearity;
- unitality;
- finite propagation;
- the degree grading;
- integrality and monomiality;
- preservation of the Bernoulli trace;
- `L^2` isometry, including von Neumann dimension over `L(G)` and any `K_0` or trace invariant of these operators;
- and triviality on the finitely generated module of one-site observables.

Such a proof would show that no `(L, R)` exists over `Z`, which contradicts (A).

- **The invariant that must be used.** Multiplicativity of `S T = (τ σ)^*`, equivalently (by (B3)) that it is a
  pullback.
- **The step where every member of the class dies.** The step is passing from `S T = id` on a finitely generated
  generating submodule, such as the one-site observables (where direct finiteness of projective `K[G]`-modules
  applies), to `S T = id` on all of `O`.
  - `O` is `K` plus infinitely many orbit modules `K[G/H]` with finite `H`. Over `Z` it contains infinitely many
    free summands, so its finite-propagation endomorphisms are not directly finite.
  - In `finite-pattern-projective-decoder-proof`, this step is the sentence "The site basis separates symbols, so
    tau sigma=id on all configurations". That sentence uses that `τσ` is a map of configurations, which is
    multiplicativity.
  - `(L, R)` are the identity on one-site observables and still strict.

**Scope.** (A) needs one element of infinite order, and Z is sofic and surjunctive. So the obstruction applies to
every argument meant to work uniformly over all groups, and to every argument for a particular group containing Z.
It says nothing about arguments that use `τ^*` as an algebra map. Examples are the relative-commutant splitting in
`quantum-endomorphisms-split-off-their-relative-commutant`, Stone-duality or clopen-counting arguments, entropy, and
the finite-pattern route, which restricts to a multiplicative invariant finitely generated piece.
