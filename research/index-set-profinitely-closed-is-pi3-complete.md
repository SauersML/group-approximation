---
rg: 2
id: index-set-profinitely-closed-is-pi3-complete
kind: claim
title: The recursively enumerable subsets of the integers that are closed in the profinite topology form a Pi-zero-three complete index set
distinct_from:
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that is a statement about groups; this is the pure computability statement about subsets of the integers that drives its three-generator sharpening.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that translates closedness of an index set into residual finiteness of a group; this classifies closedness itself.
---

ESTABLISHED.  Write `cl(J)` for the closure of `J <= Z` in the profinite
topology of `Z`:

```text
i in cl(J)   iff   for every n >= 1,  (i + nZ) meets J.
```

Then

```text
CLOSED := { e : W_e (as a subset of N <= Z) satisfies cl(W_e) = W_e }
```

is `Pi^0_3`-complete under computable many-one reductions.

The hardness family is dyadic: with `D_x = 2^x (2Z + 1)`, the odd multiples
of `2^x`, put

```text
J_e = {0} u  U_x { 2^x (2j + 1) : j < |W_g(e,x)| }.                  (IC1)
```

If every `W_g(e,x)` is finite then `J_e` is closed; if some `W_g(e,x)` is
infinite then `-2^x in cl(J_e) \ J_e`.  With `{e : for all x, W_g(e,x)
finite}` `Pi^0_3`-complete this proves hardness.

The point of the dyadic placement is that the classes `D_x` are pairwise
disjoint clopen sets whose only accumulation point in `Z-hat` is `0`, which
is put into `J_e` once and for all; a naive placement of rows in arithmetic
progressions fails because unboundedly long finite rows manufacture
closure points.
