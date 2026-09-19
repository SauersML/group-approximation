---
rg: 2
id: manzoor-cdi-source-has-no-determined-koopman-gate
kind: claim
title: The published Manzoor--CDI source has no determined Koopman gate
distinct_from:
  manzoor-separation-does-not-specify-haar-cylinders: that shows the game separation does not determine the joint stabilizer cylinders required by an abelian Haar test; this identifies the conjugation-cylinder data required by every nonabelian group-basis Koopman test and computes the standard stabilizer realization's chaos form.
  group-basis-actions-have-permutation-koopman-spectrum: that gives the general necessary condition for an equivariant group-basis embedding; this audits whether the particular published non-CE relation source supplies enough information to evaluate it.
  non-ce-property-t-equivalence-relation-exists: that establishes a non-CE relation factor by two existential embeddings; this shows neither embedding selects the pmp action or actor representation needed by the group-basis compiler.
---

Let `mu` denote the ergodic non-co-hyperlinear IRS of the free group `Gamma`
used in Manzoor's proof.  The paper does **not** determine whether the
conjugation Koopman representation

```text
kappa_mu: Gamma -> U(L^2(Sub(Gamma),mu))                (MKG1)
```

is a subrepresentation of a countable permutation representation.  It also
does not select a pmp stabilizer realization or a property-`(T)` relation
envelope whose Koopman representation could be tested instead.

There is nevertheless an exact source-side gate.  For every pmp action
`Gamma actson (X,nu)` with stabilizer distribution `mu`, the stabilizer map

```text
s:X -> Sub(Gamma),   s(gx)=g s(x) g^(-1)                (MKG2)
```

is equivariant and pushes `nu` to `mu`.  Pullback along `s` is therefore an
equivariant trace-preserving embedding

```text
L^infinity(Sub(Gamma),mu) -> L^infinity(X,nu).          (MKG3)
```

Thus `(MKG1)` is a closed subrepresentation of the Koopman representation of
**every** realization.  If `(MKG1)` is not permutation-contained, then
`group-basis-actions-have-permutation-koopman-spectrum` rules out every
equivariant embedding of every stabilizer realization into `L(K)` under an
action by automorphisms of a countable group `K`, amenable or otherwise.

The standard Abért--Glasner--Virág realization makes the remaining data
transparent.  First sample `H` with law `mu`; then independently label the
vertices of the Schreier graph `Gamma/H` by `[0,1]`, and let `Gamma` move the
root.  After choosing an orthonormal basis
`1,e_1,e_2,...` of `L^2([0,1])`, its Koopman space decomposes as

```text
integral_(H in Sub(Gamma))^⊕
  [ directSum_(finite colored patterns a on Gamma/H) C delta_(H,a) ]
  d mu(H).                                               (MKG4)
```

The empty-pattern, or zero-chaos, summand is exactly `(MKG1)`.  Higher
chaoses are measured direct integrals of the quasi-regular finite-pattern
representations.  Formula `(MKG4)` is a measured permutation model over the
generally non-atomic base `mu`; it is not by itself a permutation
representation on one countable set.

Testing even the zero chaos requires the matrix coefficients

```text
<1_A, kappa_mu(g)1_B> = mu(A intersect gB)              (MKG5)
```

for stabilizer cylinder sets `A,B`.  These are joint conjugation-cylinder
probabilities.  Manzoor's non-local-game functional uses only the character
coefficients

```text
tau_mu(w)=mu({H:w in H}),                               (MKG6)
```

and even a complete oracle for `(MKG6)` would not recover `(MKG5)`, because
the IRS-to-character map is not injective.  In the published existence proof
there is less information still: Theorem 3.13 derives the existence of some
separating game by contradiction, then the proof of Theorems 1.1--1.2
chooses an unspecified above-gap IRS and an unspecified extreme point.

This is not a harmless choice of a standard model.  Stabilizer distribution
does not determine Koopman spectrum in general: for a free group, a
Bernoulli free action and its product with an action factoring through an
irrational circle rotation both have the same IRS `delta_{e}`, while the
latter has a non-torsion eigenvalue and hence fails the countable-permutation
test.  The AGV labeled-Schreier model removes this realization ambiguity only
after `mu` itself has been supplied; Manzoor does not supply it.

The CDI step does not repair the missing datum.  Its Theorem D says that the
trivial extension `R times Delta_Y` of the first relation embeds into **some**
ergodic property-`(T)` relation `S`.  It does not present `S` as a named pmp
action of `SL_3(Z)` (or of any fixed actor) and does not give a Koopman
decomposition of its Cartan base.  It therefore cannot be evaluated against
the group-basis criterion without making an additional actor/action choice.

Hence the published Manzoor--CDI source neither passes nor fails the
permutation-Koopman gate: there is no specified representation to decide.
The first new input that would make the test executable is either

1. a named non-co-hyperlinear IRS with the joint cylinder law `(MKG5)`, after
   which `(MKG1)` can be tested; or
2. a direct non-CE pmp action with an explicit Koopman decomposition and a
   specified non-Haagerup actor.

Passing this spectral gate would remain only necessary; multiplication and
normalizer coherence are still needed for an equivariant embedding into a
group algebra.

Primary sources: Manzoor,
[*There is an equivalence relation whose von Neumann algebra is not Connes
embeddable*](https://arxiv.org/html/2502.06697v2), Theorem 2.4, Proposition
2.11, Theorem 3.13, and the proof of Theorems 1.1--1.2; Abért--Glasner--Virág,
[*Kesten's theorem for invariant random subgroups*](https://arxiv.org/abs/1201.3399),
Propositions 13--14; Chifan--Drimbe--Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/html/2205.07442),
Theorem D.
