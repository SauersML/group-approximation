---
rg: 2
id: residual-finiteness-three-generator-recursive-is-pi3-complete
kind: claim
title: Residual finiteness is Pi-zero-three complete already for three-generator recursive presentations
distinct_from:
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that needs a countable free product and leaves the finitely generated case open; this settles it at three generators through the exact closure criterion and the dyadic index sets.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that is the group-theoretic criterion; this is the complexity theorem it yields.
  mf-recognition-two-generator-recursive-is-pi2-complete: that is a second-level statement at two generators; this is a third-level statement at three generators, and the number of generators is not known to be optimal.
---

ESTABLISHED.  For recursive presentations on three generators,

```text
RF_rec3     is Pi^0_3-complete,
NONRF_rec3  is Sigma^0_3-complete,                                    (R3)
```

witnessed by the single family

```text
H_e = < a, b, s | [s, b^i a b^-i] = 1  for  i in J_e >,
J_e = {0} u U_x { 2^x (2j+1) : j < |W_g(e,x)| },
```

which is residually finite iff every `W_g(e,x)` is finite.

Consequently residual finiteness of finitely generated recursively
presented groups is strictly harder, in the arithmetical hierarchy, than
local embeddability into finite groups, soficity, hyperlinearity or
operator-MF, each of which is `Pi^0_2` on the same syntax.  The
two-generator case is open only because the profinite-closure family is
three-generated; a two-generator residually finite envelope that is
effective and preserves non-residual-finiteness of the seed (for instance an
effective form of Wilson's embedding theorem) would close it.
