---
rg: 2
id: finite-projective-sector-groupoids-have-conjugate-absorbers
kind: claim
title: Finite projective sector groupoids have stationary conjugate absorbers
distinct_from:
  projective-label-pullbacks-have-conjugate-stationary-absorbers: that treats one projective label group on one fiber; this treats sector-changing bimodules and corner returns among inequivalent finite packet types.
  finite-groupoid-diagonals-have-only-classical-gluing: that treats object diagonals and literal coarse partitions; this classifies projective K-type intertwiners and their multiplicity gauges.
---

# Finite projective sector groupoids have stationary conjugate absorbers

ESTABLISHED. Let `Gcal` be a finite groupoid. Give each object `a` a
finite-dimensional Hilbert space `V_a` and each arrow `g:a->b` a projective
unitary intertwiner

```text
C_g:V_a -> V_b,
C_h C_g=c(h,g)C_(hg),       |c(h,g)|=1.                  (SG1)
```

Then the doubled arrows

```text
T_g=C_g tensor conjugate(C_g):
    V_a tensor conjugate(V_a) -> V_b tensor conjugate(V_b)             (SG2)
```

form an honest unitary functor: the cocycles in the two tensor factors are
inverse. In particular every finite bisection of `Gcal` acts honestly on

```text
W=direct_sum_a V_a tensor conjugate(V_a).                 (SG3)
```

Let a group presentation assign one such bisection label to each occurrence,
and suppose every relator evaluates to the identity bisection. For every
ordinary contextual representation `{Y_i}` of the same presentation,

```text
R_i=T_(label_i) tensor Y_i                                (SG4)
```

is an exact representation with the prescribed sector transport. The
overhead `dim W` is fixed independently of the code size.

This applies to a finite packet with several irreducible K-types. On

```text
H=direct_sum_a V_a tensor M_a,
```

a unitary which normalizes the packet algebra permutes its central type
projections and has, on every transported block, the Schur form

```text
C_g tensor Q_g.                                           (SG5)
```

The arrows `g` and their projective compositions are precisely the finite
intertwiner groupoid. Exact unitary transport forces equal dimensions and
multiplicities along each orbit; a common finite amplification supplies the
stationary model `(SG3)`.

Compressing a labeled word to one type corner does not change the conclusion.
If its groupoid path does not return, the compression is zero. If it returns,
the corner word is one fixed finite loop matrix tensored with the multiplicity
word. A locally satisfied return relation is absorbed by `(SG2)`. Hence pure
two-sector transport cannot force a positive corner to remain attached to a
contextual code carrier; the contextual model tensors through unchanged.

The first operation outside this theorem is an **additive multi-path block**:
a corner unitary whose same block entry is a coherent sum of two or more
packet paths, rather than one groupoid arrow/bisection. Such interference is
not a projective functor and cannot be canceled arrowwise by `(SG2)`. This is
exactly the non-diagonal block-escaping operation isolated by the
signed-Hecke first-cycle chord. Merely adding a second sector, more return
loops, or finite projective holonomy remains matricial.
