---
rg: 2
id: range-local-finite-edge-authentication-is-affine
kind: claim
title: A saturated range-local finite edge can authenticate only an affine selector support
distinct_from:
  private-d8-cube-has-one-common-source: that constructs the common source and orthogonal context ranges; this classifies what an ordinary finite-edge bridge can put on one of those ranges.
  tensor-context-types-classicalize-common-source: that tensors the complete context algebras and thereby makes all pullbacks commute; this permits independent range orientations but shows that finite-edge saturation has already reduced every local predicate to affine support.
  isotypic-finite-edge-forces-full-commuting-selector-support: that proves an induced-type support statement; this adds the canonical-trace saturation argument for an HNN range bridge and identifies the perfect-LCS endpoint.
  algebraic-exhaustive-marked-type-detectors-violate-induction: that rules out exhaustive algebraic rejection detectors over all marked types; this treats one selected target range and proves that its unavoidable support is one explicit affine coset.
---

Let `E` and `A` be finite subgroups of a group `H`, with `A` elementary
abelian and

```text
[E,A]=1.                                                (RFE1)
```

Think of `E` as the finite edge packet whose type is transported from the
common D8 source, and of `A` as the commuting involutions naming one
context's Boolean variables.  Fix an irreducible representation `sigma` of
`E`.  Put

```text
I=E intersect A.                                       (RFE2)
```

Because `I` is central in `E`, it acts in `sigma` by one character `eta`.
The compatible selector characters are

```text
C_sigma={chi in A^ : chi|_I=eta}.                      (RFE3)
```

After identifying `A^` with a Boolean cube, `C_sigma` is an affine coset.
Let `e_sigma in C[E]` be the central `sigma`-projection and let `p_chi` be
the character projection in `C[A]`.

## Exact affine-support theorem

For every `chi in C_sigma`,

```text
e_sigma p_chi !=0.                                     (RFE4)
```

In fact the canonical group trace gives the explicit packet constant

```text
tau(e_sigma p_chi)
 =dim(sigma)^2 |I|/(|E||A|)              (chi in C_sigma).  (RFE4a)
```

Consequently, if `R subset A^` is the allowed set of a context and a
selected target projection `q in C[H]` satisfies

```text
e_sigma<=q<=p_R:=sum_(chi in R) p_chi,                 (RFE5)
```

then necessarily

```text
C_sigma subset R.                                     (RFE6)
```

Thus a saturated finite edge cannot cut out an arbitrary nonlinear support.
It can only select a union containing its entire compatible affine coset.
Adding more selector elements to the edge shrinks the coset by adding
linear parity equations.  At the extreme it fixes one classical assignment.

## Why canonical matrix saturation is already exact saturation

Let `E_0` be an isomorphic source edge, let `sigma_0` correspond to `sigma`,
and suppose an HNN/graph-of-groups stable word `t` conjugates the complete
edge tables.  Then in the group algebra

```text
t e_(sigma_0) t^(-1)=e_sigma.                          (RFE7)
```

The proposed range-local decoder needs the transported source to land in
the selected context carrier:

```text
||(1-q)t e_(sigma_0)||_2=o(1).                         (RFE8)
```

This cannot be a merely asymptotic bonus of canonical matrix models.  For
canonical microstates the square of the left side converges to

```text
tau_Gamma(e_sigma(1-q)e_sigma).                        (RFE9)
```

The canonical group trace is faithful.  Hence `(RFE8)` forces
`e_sigma<=q` in `L(Gamma)`.  If the advertised finite target packet `H`
embeds, its group algebra embeds faithfully as well, so this is precisely
the algebraic containment in `(RFE5)`.  If `(RFE5)` fails, the positive
number in `(RFE9)` is a fixed normalized-HS leakage floor, independent of
matrix dimension.  Orthogonality of the different context ranges does not
alter this one-range calculation.

More explicitly, if one compatible `chi` is rejected and `q<=p_R`, then

```text
tau_Gamma(e_sigma(1-q)e_sigma)
 >=dim(sigma)^2 |I|/(|E||A|).                         (RFE9a)
```

Thus the obstruction is not qualitative: the proposed bridge misses a
computable positive fraction of its source before any long word or ambient
matrix dimension enters.

This closes the tempting finite-edge version of the range-local escape:

```text
common source Q
 -> ordinary HNN edge t_c
 -> selected context range q_c
```

either leaks a fixed amount of `Q`, or its local selector support contains
an affine coset.

## The perfect-LCS endpoint

Apply the conclusion to every context of a fixed BCS.  If the exact
commuting witness extends the range-local packet and the consistency rows
identify shared variables on the common source, the pulled-back selectors
obey the affine equations defining the cosets `C_(sigma,c)` and every such
coset lies in the original allowed relation.  They therefore form a perfect
commuting strategy for an affine, hence linear-constraint-system, subgame of
the original BCS.

The finite-dimensional gap is inherited with a fixed modulus: a strategy
which nearly satisfies the affine subgame satisfies the original predicate
whenever the affine equations hold, and the consistency tests are the same.
Thus a range-local finite-edge compiler which succeeds through `(RFE8)` has
already constructed a perfect-commuting/finite-dimensional-gap LCS.  Its
solution group is the standard known terminal route to a non-hyperlinear
group.

In particular:

- if every compatible coset is a singleton, exact consistency gives one
  global classical satisfying assignment, impossible for the intended
  nonclassical gap instance;
- if a nontrivial compatible coset survives, the substantive new object is
  already the perfect-gap LCS, not an easier finite-packet authentication;
- if a context's allowed relation contains no compatible coset for the
  chosen edge data, the bridge has the fixed leakage `(RFE9)`.

## Remaining honest escape

The theorem does not rule out a genuinely finite-matrix-only actuator.  Such
an actuator may charge the leakage by cyclic finite trace, integer
multiplicity, a proper-corner return, or a common Gram saturation law which
fails in induced infinite representations.  It does rule out obtaining the
needed source-to-selected-range promotion from finite subgroup
exactification and ordinary algebraic HNN restriction data alone.
