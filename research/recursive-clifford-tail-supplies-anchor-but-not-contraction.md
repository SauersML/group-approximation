---
rg: 2
id: recursive-clifford-tail-supplies-anchor-but-not-contraction
kind: claim
title: A recursive Clifford tail supplies the identity-outer anchor exactly but not the strict contraction
distinct_from:
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that proves a same-gauge identity-outer occurrence cancels the CZ twist; this constructs such occurrences coherently at every binary depth and identifies the additional exposure inequality needed for contraction.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that gives an affine countermodel to bare prefix cloning; this retains the genuinely nonlinear CZ outer action and shows that finite-depth Clifford regular packets are still stationary.
  contractive-computation-ladder: that sums an already supplied scalar recurrence; this derives that recurrence from a recursive anchor plus one explicit strict payload-exposure hypothesis.
  thompson-clifford-central-product-tape: that supplies finitely presented Pauli sites, a common sign and subtree transport; this supplies an exact tail-gate completion but does not assert that the tail gates already have a finite presentation.
---

**ESTABLISHED REDUCTION AND COMPLETENESS MODEL.**  The arbitrary
multiplicity twist can coherently become the semantic gate at the next level.
There is an exact properly infinite model in which this happens at every
vertex.  However, the resulting recursion is mass-preserving.  A strict
contractive recurrence follows only after a separate, matrix-only
payload-exposure estimate with coefficient below one.

## Exact binary-tree tail anchor

Let `X={0,1}^*`.  At each vertex `x` put one two-qubit Hilbert space
`H_x=C^4`, the reference vector `xi_x=|00>`, and the controlled-Z involution
`C_x`.  Since `C_x xi_x=xi_x`, the incomplete tensor product

```text
H=restrictedTensor_(x in X) (H_x,xi_x)                 (RCT1)
```

admits the infinite subtree products

```text
T_x=product_(y has prefix x) C_y.                      (RCT2)
```

Indeed every elementary tensor differs from the reference tensor at only
finitely many sites, so all but finitely many factors in `(RCT2)` act as the
identity on that vector.  Thus `T_x` extends to a well-defined unitary
involution.  Products belonging to disjoint subtrees commute, and the exact
partition of a subtree gives

```text
T_x=C_x T_(x0)T_(x1).                                  (RCT3)
```

Put

```text
A_x=T_(x0)T_(x1).                                      (RCT4)
```

Relative to the local Pauli packet at `x`,

```text
T_x=C_x tensor V_x,       A_x=I_x tensor V_x,          (RCT5)
V_x=T_(x0)T_(x1).
```

Consequently

```text
T_x A_x=C_x.                                           (RCT6)
```

This is precisely the same-gauge identity-outer anchor required by the
prefix support row.  It is self-recursive: the gauge at `x` is the product
of the two semantic child tail gates.  Local Pauli pairs at different
vertices commute and their same-site commutators are the common scalar
`-I`, so `(RCT1)--(RCT6)` are compatible with the central-product Clifford
tape.  They give an exact representation in the properly infinite algebra
`B(H)` and hence an exact noncollapse/completeness witness for the recursive
anchor identities.

The construction deliberately does not claim that the subtree-tail
operators belong to the product-trace von Neumann algebra: infinite products
of fixed nontrivial trace-distance need not converge there.  Completeness is
operator-algebraic; finite presentation and matrix soundness remain separate.

## Sufficient recursive exposure lemma

Let `E in [0,1]` be the global squared relator energy and let `a_n>=0` be the
unresolved marked mass at level `n`, uniformly bounded.  Suppose fixed-word
exactification supplies at every level:

1. a good anchored mass `g_n` and boundary mass `b_n` satisfying

   ```text
   a_n<=lambda a_(n+1)+g_n+b_n,       0<lambda<1;       (RCT7)
   ```

2. a polynomial `p` and constants `B,D` independent of matrix dimension
   such that

   ```text
   b_n<=B p(n)sqrt(E),
   delta_n<=D p(n)sqrt(E);                              (RCT8)
   ```

3. on the good mass, `T_x,A_x` decode `(RCT5)` with error `delta_n`, so the
   coarse/fine selector floor gives

   ```text
   g_n<=4 delta_n^2.                                    (RCT9)
   ```

Then, because `E<=sqrt(E)` on `[0,1]`,

```text
a_n<=lambda a_(n+1)
     +(B p(n)+4D^2 p(n)^2)sqrt(E).                     (RCT10)
```

The parenthesized coefficient is polynomial.  Therefore
`contractive-computation-ladder` applies verbatim.  If marked separation
gives `a_0>=a_*>0`, there is a dimension-independent positive lower bound on
`E`.

This is the rigorous self-recursive compiler interface.  The tail identities
solve the same-gauge part `(RCT9)`.  All remaining soundness is concentrated
in the strict exposure clause `(RCT7)`: at least a fixed fraction `1-lambda`
of unresolved mass must enter the anchored good region or an already charged
boundary at every positive-density set of levels.

## Why recursion alone cannot supply `lambda<1`

Equations `(RCT3)--(RCT6)` are products of unitaries and conserve the whole
carrier.  They contain no proper corner, rejection projection, or
non-bijective incidence.  Accordingly they admit stationary finite-depth
models.

Truncate the binary tree below depth `N`.  The finitely many local Pauli and
Clifford gates generate a finite group.  Define each truncated `T_x` as the
product of descendant `C_y` through depth `N`; then `(RCT3)--(RCT6)` hold
exactly at every level `<N`.  The negative-central summand of the regular
representation of this finite group has positive mass and zero local defect.
Subtree permutations make all equal-depth carrier masses stationary.

Thus arbitrarily deep exact local models have

```text
a_n=a_(n+1)>0,       g_n=b_n=E=0                       (RCT11)
```

for the recursion-only bookkeeping.  No universal deduction of `(RCT7)`
with `lambda<1` is possible.  This is the Clifford analogue of the affine
clone countermodel: nonlinear outer action defeats the affine realization,
but finite regular type flow still defeats absorption.

Consequently the recursive identity-outer anchor is a genuine completeness
advance and a sharp simplification of the soundness target, not itself a
contraction mechanism.  A successful packet extension must add a
payload-dependent first-hit, contextual collision, or proper-corner capacity
law establishing `(RCT7)` only in finite matrices.  Adding more subtree
copies, swaps, or covariance tables leaves `(RCT11)` intact.
