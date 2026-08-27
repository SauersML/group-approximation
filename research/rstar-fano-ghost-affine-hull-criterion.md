---
rg: 2
id: rstar-fano-ghost-affine-hull-criterion
kind: claim
title: The seven-point one-ghost relation is non-Schaefer and its affine failure is exactly a Fano line
distinct_from:
  tracial-support-affine-linearization: that affine-linearizes an arbitrary tracial context support; this identifies exactly when affine linearization of the specific seven-point relation stays inside the nonlinear predicate.
  linear-encoding-lcs-admits-odd-subset-cheats: that gives general odd-subset characters of a linear encoding; this classifies the complete odd-subset obstruction for one fixed four-bit relation by Fano incidence.
---

ESTABLISHED.
Let

```text
H={x in F_2^4: x_1+x_2+x_3+x_4=1},
g=(1,0,0,0),
R_*=H\{g}.                                                       (RFG1)
```

Then the one-relation Boolean language `{R_*}` is non-Schaefer and hence its
classical CSP is NP-complete.  More precisely, translation by `g` identifies
`R_*` with the seven nonzero points of the three-dimensional vector space

```text
V=H+g={v in F_2^4: sum_i v_i=0}.                                (RFG2)
```

For every `S subseteq R_*`, writing `T=S+g subseteq V\{0}`, the following
are equivalent:

```text
g in Aff(S),
0 in Aff(T),
T contains {u,v,u+v} for two distinct nonzero u,v,
S contains a Fano line after translation by g.                    (RFG3)
```

Consequently

```text
Aff(S) subseteq R_*  iff  S+g is a Fano cap.                      (RFG4)
```

In the coordinates of `(RFG1)`, the seven minimal bad triples are exactly

```text
{0001,0010,1011},  {0001,0100,1101},  {0001,0111,1110},
{0010,0100,1110},  {0010,0111,1101},  {0100,0111,1011},
{1011,1101,1110}.                                           (RFG4a)
```

Thus a proposed support certificate is finite: it must delete at least one
atom from each triple in `(RFG4a)` in every context.

This gives an exact local escape from the affine-predicate barrier: any
perfect strategy whose support in every `R_*` context is a Fano cap remains
perfect after replacing that support by its affine hull, and every solution
of the resulting affine context equations still satisfies the original
nonlinear predicate.

The conclusion is support-dependent.  It does not by itself select one cap
profile uniformly from a presentation or force approximate matrix supports
to prune to caps.

## NP-hardness witnesses

The seven points are

```text
0100,0010,0001,1110,1101,1011,0111.                              (RFG5)
```

The relation is neither zero-valid nor one-valid.  It is not affine because
it has seven elements.  It is not Horn since
`1110 AND 1101=1100`, not dual-Horn since `0100 OR 0010=0110`, and not
bijunctive since the coordinatewise majority of `1110,1101,1011` is `1111`.
Schaefer's dichotomy therefore gives NP-completeness.

Claims that all twelve arity-three derived nonconstant hyperplanes are
bijunctive and all fifty-six arity-four ones are NP-hard require the precise
derivation convention and an explicit finite certificate table.  Those
enumeration counts are not used in `(RFG1)--(RFG4)` and are not asserted
here.  Accordingly `R_*` is called *one-ghost minimal* only in the literal
sense that it deletes one point from its affine hull, not inclusion-minimal
among NP-hard relations.
