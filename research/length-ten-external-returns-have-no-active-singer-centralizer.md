---
rg: 2
id: length-ten-external-returns-have-no-active-singer-centralizer
kind: claim
title: External-return words through length ten have no active Singer centralizer
artifacts:
  - experiments/mixed_external_return_centralizer_search.py
distinct_from:
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts single external roots under the two Whitehead and Singer heads; this exhausts all products of the eight roots through reduced word length ten and tests direct commutation with each complete Singer head.
  el20-six-moving-coefficient-square-bridges: that permits arbitrary coefficient-sensitive EL20 words; this is only a finite constant-root label-matrix fence and does not exclude longer words or nonconstant Leavitt coefficients.
---

**ESTABLISHED BOUNDED CONSTANT-ROOT FENCE.**  In the seven-coordinate
binary label representation of the signed Hecke packet, let `X` be the
eight external root transvections of
`signed-hecke-normalizer-has-eight-external-root-returns`.  For row `i`,
let `t_i` be the complete Singer head and let `S_i` be the subgroup generated
by `L_0` and the two external roots fixed by `t_i`:

```text
S_1=<L_0,x_59(1),x_96(1)>,
S_2=<L_0,x_27(1),x_74(1)>.                            (LTC1)
```

Then every element represented by an `X`-word of length at most ten which
commutes with `t_i` belongs to `S_i`:

```text
g in <X>, length_X(g)<=10, [g,t_i]=1  ==>  g in S_i. (LTC2)
```

Both spectator subgroups in `(LTC1)` have order `32768`.  Breadth-first
enumeration visits, for each row, respectively

```text
9,47,191,677,2159,6295,16901,42184,97680,208137      (LTC3)
```

distinct matrices through depths one to ten.  At every depth the number of
centralizers outside `S_i` is zero.  The identical counts in the two rows
come from their coordinate symmetry; the membership and commutator tests
are performed separately with the two literal Singer matrices.

Thus the shortest remaining bridge search cannot be closed by replacing a
single external return with any constant-root product of length at most ten
which directly commutes with the full Singer head.  A live word must be
longer, use nonconstant Leavitt coefficients, or return through a genuinely
mixed relation weaker than direct commutation.  This statement does not
authenticate reservoir gauges and is not a representation of full EL20.

No Property `(T)`, Kazhdan input, trace profile, stability theorem,
literature result, local compilation, or local computation is used.

DERIVATION
length-ten-external-return-centralizer-enumeration
