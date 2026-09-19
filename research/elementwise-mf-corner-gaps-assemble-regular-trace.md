---
rg: 2
id: elementwise-mf-corner-gaps-assemble-regular-trace
kind: claim
title: Elementwise MF corner gaps assemble into simultaneous regular-trace tables
distinct_from:
  mf-invariant-corner-visibility: that is the open existence statement supplying one positive trace gap for each element; this is the finite assembly theorem after those separate gaps have been supplied, and does not assert they exist for every MF group.
  adaptive-tensor-amplification: that starts from operator-norm separation and pays an exponent linear in the unknown matrix dimension; this starts from dimension-free trace gaps, first combines models belonging to different elements, and uses an exponent independent of all input dimensions.
  character-diracization-limit: that tensor-powers one exact character and identifies its pointwise limiting kernel; this handles approximate operator-norm multiplication tables, preserves their norm separation, and assembles separately chosen tables before taking a power.
  balanced-replica-hs-amplification: that controls normalized-Hilbert--Schmidt defect for one balanced table; this controls operator-norm defect for a direct sum of different tables and uses identity padding to remove scalar phases.
---

**ESTABLISHED FINITE ASSEMBLY THEOREM.**  Let `F` be a finite group-word
window containing `1`, let `R` be a finite set of multiplication tests
`ab=c` inside `F`, and enumerate nonidentity test words as

```text
K={g_1,...,g_m} subset F.                                  (EGA1)
```

Suppose unitary tables

```text
phi_i:F->U(d_i),             i=0,...,m,
```

send `1` to the identity and have operator-norm defect at most `delta` on
`R`.  Assume the base table retains prescribed norm separation

```text
||phi_0(g_i)-I||_op >= alpha_i,                            (EGA2)
```

and the table indexed by `i` has one dimension-free trace gap

```text
Re tr_(d_i)(phi_i(g_i)) <= 1-c_i,       c_i>0.             (EGA3)
```

Put `M=m+1`.  For every integer `p>=1` there is one unitary table `Phi_p`
such that

```text
Def_R(Phi_p) <= p delta,
||Phi_p(g_i)-I||_op >= alpha_i,
|tr(Phi_p(g_i))| <= exp(-p c_i/(4M))       for every i.    (EGA4)
```

Thus, for fixed positive gaps `c_i` and `0<eta<1`, choosing

```text
p >= (4M/min_i c_i) log(1/eta),        delta<=epsilon/p    (EGA5)
```

produces a single `epsilon`-multiplicative operator-norm table which keeps
all the original norm separations and has `|tr(Phi_p(g))|<=eta`
simultaneously for every `g in K`.

## Consequence for invariant-corner visibility

The corner-free formulation `(I')` of
`mf-invariant-corner-visibility` is therefore already equivalent, at the
group-table level, to trace-controlled operator MF with the regular
character.  Indeed, on a fixed finite window choose one `(I')` model for
each nonidentity test word, add one ordinary faithful MF model as `phi_0`,
and apply `(EGA4)--(EGA5)`.  Diagonalizing over windows gives operator-norm
models which remain faithful and whose normalized traces converge to the
regular character.

Conversely such simultaneous regular-trace tables satisfy `(I')` directly,
with `P=1`.  Hence there is no additional finite-family compatibility gap
between elementwise invariant-corner visibility and simultaneous trace
control.  The unsolved content remains exactly the production of the first
dimension-free elementwise gap from weak MF data.
