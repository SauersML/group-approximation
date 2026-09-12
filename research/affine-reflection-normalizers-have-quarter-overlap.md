---
rg: 2
id: affine-reflection-normalizers-have-quarter-overlap
kind: claim
title: Every finite affine reflection-normalizer gadget has a regular quarter-overlap model
distinct_from:
  odd-leavitt-reflections-retain-stationary-xor-overlap: that gives the smallest S4 model for one parent/child connector; this treats an arbitrary finite family of commuting reflection words and finite normalizer rows at once.
  coupled-reflections-reduce-to-the-active-gauge-profile: that reduces arbitrary packet normalizers to a residual multiplicity presentation and leaves open whether that presentation has models; this gives an exact regular stationary model whenever the residual support language is affine over finitely many involutions.
  finite-packet-flow-keeps-payload-orientation-balanced: that treats stationary multiplicity flows in finite subgroup/HNN diagrams; this computes the exact projection overlap retained by the entire affine reflection-normalizer class.
  payload-conditioned-btb-active-fiber-floor: that permits a genuinely non-semisimple global coefficient-occurrence row; this rules out only finite affine reflection products and normalizers, not that remaining row.
---

**ESTABLISHED REGULAR STATIONARY COUNTERMODEL.** Let `V` be a nonzero
finite-dimensional vector space over `F_2`, write its additive group as

```text
A={a_v:v in V},          a_v a_w=a_(v+w),
```

and let `K<=GL(V)`.  In the finite affine group

```text
H=A rtimes K                                               (FAR1)
```

put, in its left regular representation,

```text
R_v=lambda(a_v),             P_v=(1-R_v)/2.              (FAR2)
```

Then every reflection-product and normalizer row is literal:

```text
R_v R_w=R_(v+w),
lambda(k)R_v lambda(k)^*=R_(kv),
lambda(k)P_v lambda(k)^*=P_(kv).                         (FAR3)
```

For every nonzero `v`, and every pair of distinct nonzero `v,w`, the regular
trace satisfies

```text
tau(P_v)=1/2,
tau(P_v P_w)=1/4,
tau(P_v(1-P_w))=tau(P_w(1-P_v))=1/4.                    (FAR4)
```

This follows by expanding the projections: `a_v`, `a_w`, and `a_(v+w)`
are all nonidentity, so every nonconstant Fourier coefficient has regular
trace zero.  More generally, the joint atom cut out by `r` linearly
independent reflection signs has trace `2^(-r)`.  Hence the uniform Boolean
distribution is stationary under every finite family of linear normalizers.

The proper-corner consequence is exact.  Suppose a proposed refinement uses
nonzero `p,e in V`, `p!=e`, writes the parent reflection as

```text
R_q=R_p R_e,               q=p+e,                       (FAR5)
```

and contains a connector `k in K` with `kq=p`.  Equations `(FAR3)` give the
advertised ordinary-word rows

```text
R_q=R_pR_e,                 kR_qk^(-1)=R_p              (FAR6)
```

with zero defect.  Nevertheless the alleged child and parent support cuts
are not nested:

```text
tau(P_p(1-P_q))=tau(P_q(1-P_p))=1/4.                   (FAR7)
```

Equivalently, the word rows remember symmetric difference (XOR), not
orthogonal union or inclusion.  Common matrix amplification preserves all
numbers in `(FAR4)--(FAR7)`.

This supplies a countermodel for every **finite affine reflection-normalizer
compiler**: finitely many protected commuting involution words, finitely many
relations identifying their products, and finitely many connector words
whose conjugation action on those involutions is linear.  Take `V` to be the
finite span of all named signs and `K` the finite subgroup of `GL(V)` generated
by their prescribed actions.  Whenever the listed word relations are
consistent in this affine action, `(FAR1)` realizes all of them exactly.
Finite packet/projective decorations may be tensored on independently; a
fixed finite phase is cancelled by its inverse finite Weyl module, and the
regular `A`-trace is unchanged.

The countermodel is payload-stationary as well.  Tensor `(FAR1)` with any
exact outer packet model and a positive selected projection `F` commuting
with the affine coordinate.  On `F` the two mismatch corners in `(FAR7)`
have trace `tau(F)/4`, while every affine reflection and connector relator
still has zero compressed defect.  Thus positive forbidden payload mass does
not orient an affine support recurrence.

**Boundary.**  This does not refute `(BAF3)` in full.  It leaves exactly two
possibilities already isolated there:

1. a residual active gauge presentation with no finite/asymptotically exact
   model separated from its support word (a normalized-HS profile of
   nonhyperlinearity strength); or
2. a genuinely non-semisimple global coefficient-occurrence row which does
   not reduce to products and finite automorphisms of commuting reflections.

It does rule out adding any finite depth of extra XOR refinements, finite
reflection normalizers, finite Clifford phases, or affine connector copies:
all merely enlarge `V` and `K`, and the same regular stationary model applies.

DERIVATION
regular-affine-boolean-action-fences-finite-support-rows
