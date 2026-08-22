---
rg: 2
id: approximate-bernoulli-lamp-extraction-is-cartan-completion
kind: claim
title: Approximate Bernoulli-lamp extraction still requires invariant diagonal completion
distinct_from:
  exact-bernoulli-lamp-trace-forces-actor-residual-finiteness: that succeeds because exact finite representations already permute the full character multiset; this records why the same proof does not apply to an arbitrary tracial matrix-ultraproduct embedding.
  invariant-cartan-completion: that states the open diagonal-completion theorem for the Kun--Thom crossed product; this identifies the proposed general Missing Lemma A with that gate rather than asserting it.
---

**ESTABLISHED AUDIT / REDUCTION.**  Consider a trace-preserving embedding

```text
Theta:L^infinity({-1,1}^X) rtimes H -> product_U M_(d_n).
```

Finite families of lamp projections can be represented by finite diagonal
algebras, and the crossed-product relations imply normalized-HS approximate
transport by chosen lifts of the actor unitaries.  This yields finite weighted
atomic measures with asymptotically equivariant transport, but not coherent
multiplicative permutation actions.

The exact character proof cannot be applied: a lift of `Theta(u_g)` need only
normalize the represented lamp algebra **modulo the ultrafilter**.  The lamp
algebra can be a proper subalgebra of every chosen diagonal algebra, and the
unitary may mix its growing multiplicity fibers.  Exactifying one generator
or one finite window does not produce one diagonal algebra simultaneously
normalized by all actor words.

The claimed upgrade in “Missing Lemma A” is therefore an additional Cartan
extraction hypothesis.  In the Kun--Thom setting, it supplies exactly the
content required by `invariant-cartan-completion`: after conjugacy, place the
whole Bernoulli algebra in a diagonal ultraproduct normalized by all actor
unitaries.  Then `diagonal-normalizer-rigidity` turns those normalizers into
permutations (up to diagonal phases), yielding the forbidden sofic action.

Accordingly Fourier weak-* convergence and Portmanteau are valid **after** an
exact finite action has been extracted, but they do not perform the
approximate-to-exact extraction.  Treating the approximate normalizers as a
finite `H`-set assumes the principal open non-Cartan exclusion rather than
proving it.

There is a related hardness boundary, but it must be stated with the correct
permanence direction.  If `H` is hyperlinear, hyperlinearity of
`(direct_sum_H C_2) rtimes H` is **not** supplied by the theorem that an
extension of a hyperlinear normal subgroup by an amenable quotient is
hyperlinear: here the quotient is `H`, not the amenable lamp kernel.  Known
wreath-product permanence assumes the actor is sofic.  Thus a universal
Missing Lemma A would classicalize every Bernoulli crossed product already
known to be Connes embeddable, and it contains the actor-classicalization gate
of `simple-lamp-gauge-rigidity-reduces-to-actor-classicalization`; it does not
alone prove `hyperlinear => sofic` without the additional, comparably hard
crossed-product embeddability premise.
