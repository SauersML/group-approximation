---
rg: 2
id: wagon-wheel-stops-before-bcs-groupification
kind: claim
title: Bounded wagon-wheel pictures quantify fixed group words but do not groupify a nonaffine BCS predicate
distinct_from:
  slofstra-solution-group-embedding-preserves-marked-involutions: that is the exact embedding theorem; this identifies its full dimension-free normalized-HS content and the earlier BCS-to-group datum it cannot create.
  marked-approximate-radical-survives-solution-group-embedding: that transfers an approximate-radical source word already present in a group; this gives a finite BCS-to-group decoder sufficient to manufacture such a source and proves why direct local wagon-wheel rows cannot satisfy it for a nonaffine predicate.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that characterizes trace-specific affine-safe supports; this proves the corresponding scalar boundary obstruction for every direct local wagon-wheel compiler and separates it from the one-way bounded-area estimate.
  wagon-wheel-exact-radical-has-hs-wall: that proves exact finite-dimensional invisibility of the distinguished sign in the motivating wagon-wheel output has no normalized-HS modulus; this identifies the separate pre-wagon BCS decoder that bounded picture area cannot create.
---

**ESTABLISHED QUANTITATIVE AUDIT AND SHARP LOCAL OBSTRUCTION.**  Slofstra's
wagon-wheel construction is already dimension-uniform for the operation it
actually performs.  Let `G=<Y|R>` be its finitely presented source and let
`Gamma=<S|T>` be the output solution group.  Each substituted source relator
has a fixed van Kampen expression

```text
iota(r)=product_(j=1)^A g_j t_j^(sign_j) g_j^(-1),     t_j in T.  (WW1)
```

For every map `rho:S->U(d)`, normalized Hilbert--Schmidt invariance and
telescoping give

```text
||rho(iota(r))-1||_2
  <= sum_(j=1)^A ||rho(t_j)-1||_2.                    (WW2)
```

The same estimate applies to the fixed word identifying the marked source
involution with the solution-group sign.  Because there are only finitely
many source relators, `(WW2)` gives a dimension-independent linear bound from
output presentation defect to the defect of the restricted source tuple.
For the displayed wagon wheel of a collegial relator of length `l`, one may
take the fixed filling with `3l` vertices.  This is precisely the quantitative
content used by
`marked-approximate-radical-survives-solution-group-embedding`.

The constellation/picture-surgery proof of injectivity adds no reverse
matrix decoder.  It starts with an **exact** van Kampen picture witnessing
that an output word is algebraically trivial and simplifies that picture.
Small normalized-HS norm of a matrix word supplies no van Kampen picture.
Moreover the number of constellation surgeries depends on the input picture,
not only on the fixed presentation.  Thus bounded local picture area proves
`(WW2)` for known word identities; it does not turn a small additive
projection failure mass into a word identity.

There is also no hidden compactness upgrade from exact finite-dimensional
invisibility. `wagon-wheel-exact-radical-has-hs-wall` records the sharp
counterexample inside Slofstra's own motivating output: every exact
finite-dimensional representation kills its sign, yet permutation tuples
with presentation defect tending to zero keep that sign at normalized-HS
distance `sqrt(2)`. Reindexing realizes any prescribed vanishing error
schedule. Hence the fixed-area estimate preserves an already established
source collapse modulus but cannot manufacture one from exact invisibility.

## A finite quantitative lemma that would suffice

Fix the finite tracially satisfiable but non-`R^U` BCS `B`.  It is enough to
construct a finitely presented group `G_B`, a central involution `j`, fixed
words decoding the shared BCS variables, and constants `c,C>0` with the
following two properties.

1. `G_B` has an exact finite-tracial representation in which `j=-1` and the
   decoded shared tuple is a perfect representation of `B`.
2. From every finite-dimensional approximate representation `rho` of `G_B`,
   spectral rounding produces a reducing projection `Q_rho` and one shared
   rounded tuple `Z(rho)` on `Q_rho` such that

   ```text
   E_str(Z(rho))+V_B(Z(rho)) <= C sqrt(E_G(rho)),       (WW3)
   tr_d(Q_rho) >= c||rho(j)-1||_2^2-C sqrt(E_G(rho)).  (WW4)
   ```

Here `V_B` is the sum of the forbidden joint spectral masses from the original
shared contexts, not masses of independently copied contexts.  These are
finite, dimension-uniform estimates.

Indeed, a sequence with `E_G(rho_k)->0` and `rho_k(j)` bounded away from one
has, by `(WW4)`, a nonzero tracial-ultraproduct corner.  Equation `(WW3)` gives
on that corner a perfect `R^U` representation of `B`, contradicting the source
choice.  Hence `j` is in the approximate radical but is nontrivial by property
1.  Applying Slofstra's wagon-wheel embedding and `(WW2)` then gives a
nonhyperlinear solution group.  No quantitative constellation theorem beyond
the existing fixed fillings is needed.  The entire missing input is `(WW3)`:
a shared BCS-to-group decoder before the wagon wheel.

## Exact affine obstruction to the direct local compiler

There is a zero-defect obstruction to obtaining `(WW3)` by replacing each
nonaffine context with a finite local wagon-wheel/LCS fragment.  Let
`A subset F_2^m` be the allowed assignments of one context, retain the same
visible variable at every occurrence, and allow any finite number of private
Boolean LCS auxiliaries.  Scalar `J=-1` solutions of the resulting finite
linear system form an affine subset `L` of all visible and auxiliary bits.
Their visible restrictions form the affine set

```text
P=projection_visible(L).                               (WW5)
```

Suppose exact local completeness lets every assignment in `A` extend to a
scalar solution, while exact local soundness (the zero-defect case of `(WW3)`)
allows no forbidden visible assignment.  Then

```text
A subseteq P subseteq A,
```

so `A=P` is affine.  If `A` is nonaffine, `P` contains
`Aff_F2(A)` and hence contains some `a_* in Aff_F2(A)\A`.  This is an exact
one-dimensional output model with presentation defect zero and forbidden
mass one, directly contradicting `(WW3)`.  Adding bounded wagon-wheel
substitutions cannot change `(WW5)`, because their scalar equations are still
linear and projection of an affine solution set is affine.

For a trace-specific compiler one need preserve only the actual local support
`S` of the chosen perfect trace, rather than every assignment in `A`.  The
same proof says that its exact scalar boundary packet contains `Aff_F2(S)`;
soundness is possible exactly when

```text
Aff_F2(S) subseteq A.                                  (WW6)
```

This is the locally affine-support condition already known to be equivalent
to the perfect LCS/nonhyperlinear endpoint.  Therefore the wagon wheel has no
unused quantitative reserve capable of bypassing perfect LCS completeness:
either one first proves the trace-specific condition `(WW6)`, or one supplies
a genuinely nonlocal/noncommuting groupification proving `(WW3)`.  Local
bounded-area picture surgery alone admits the exact affine-ghost countermodel.

DERIVATION
wagon-wheel-bcs-boundary-proof
