---
rg: 2
id: class-two-tanner-contextual-model-proof
kind: route
title: Count the untested commutators in the maximal class-two quotient
target: positive-rate-tanner-tests-have-contextual-models
requires: []
---

Let `V=F_2^E`.  Extend every local dual check by zero and put

```text
R=span{C_j^perp : j in J} <= V,       W=V/R.                (CTC1)
```

Then `C=R^perp`, so `dim W=dim C=k`.  Write `bar e_s` for the
image in `W` of the coordinate vector at `s`, and set

```text
L=sum_j Lambda^2 span{bar e_s : s in S_j} <= Lambda^2 W.   (CTC2)
```

The dimension bound in `(PRC1)` gives

```text
dim L <= |J| binom(q,2).                                   (CTC3)
```

Consider the universal group on involutions `x_s` with the following
relations: variables in one `S_j` commute, and for every
`h in C_j^perp` their commuting product `prod_s x_s^{h_s}` is one.  Its
maximal class-two quotient has commutator space

```text
[Gamma_2,Gamma_2] = (Lambda^2 W)/L,                         (CTC4)
```

and

```text
[x_s,x_t] = bar e_s wedge bar e_t mod L.                   (CTC5)
```

For completeness, start from the free class-two group on involutions
`x_s`.  It has normal forms indexed by
`V direct-sum Lambda^2 V`; its central commutators are the second summand.
Local jointness kills `Lambda^2 span{e_s:s in S_j}`.  Because a local parity
word is now a product of commuting generators, killing its linear vector
`r in R` and all of its conjugates kills exactly `R wedge V`.  The remaining
central quotient is

```text
Lambda^2 V /(R wedge V + sum_j Lambda^2 span(S_j)),
```

which is `(CTC4)`.  This also constructs `Gamma_2` as a finite class-two
two-group, so no representation-existence or approximation issue remains.

Choose `B subset E` such that `{bar e_s:s in B}` is a basis of `W`.  The
`binom(k,2)` wedges belonging to pairs from `B` are linearly independent.
At most `dim L` of them can lie in `L`; hence at least

```text
M=binom(k,2)-|J|binom(q,2)                                  (CTC6)
```

unordered coordinate pairs have a nontrivial commutator in `Gamma_2`.

Use the left regular representation of this finite group and put
`Q_s=lambda(x_s)`.  These are reflections.  A nontrivial commutator `z` is a
nonidentity regular permutation, so

```text
||[Q_s,Q_t]||_2^2=||I-lambda(z)||_2^2=2.                  (CTC7)
```

Counting both orientations of the `M` pairs proves `(PRC3)`.  Within each
context the `Q_s` commute and obey every dual parity check.  Their joint
spectral PVM is therefore supported on `C_j`.  On an overlap, both local PVMs
coarsen to the canonical joint spectral measurement of the same global
reflections, so full overlap consistency is exact.

Finally, if `{P_s}` commute, then

```text
||[Q_s,Q_t]||_2 <= 2||Q_s-P_s||_2+2||Q_t-P_t||_2.
```

Squaring and averaging gives
`E_(s,t)||[Q_s,Q_t]||_2^2 <=16 E_s||Q_s-P_s||_2^2`.
Together with `(PRC3)` this proves `(PRC4)`.
