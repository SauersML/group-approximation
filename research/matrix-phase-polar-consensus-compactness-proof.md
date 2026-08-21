---
rg: 2
id: matrix-phase-polar-consensus-compactness-proof
kind: route
title: Polar consensus turns almost-everywhere orientation into one abelian limit
target: matrix-phase-noncommutative-alpha-plane-route
requires:
  - phased-translations-reduce-to-alpha-plane-test
---

The `4 x 4` tensor-square ledger `(NC8)--(NC14)` uses six alpha-query errors
and a bounded swap ledger of pairwise-independent interior forms.  It proves
uniformly in the basepoint

```text
sup_t E_(b,c)||C_t(b)-C_t(c)||_2^2 <=15000(A(R)+I(R)).       (MPC1)
```

The variance and polar identities `(NC15)--(NC21)` therefore give polar means
`P_t` with

```text
sup_t E_b||P_t-C_t(b)||_2^2 ->0,
E_t||P_t-R_t||_2^2 ->0                                      (MPC2)
```

along every sequence for which `I(R)+A(R)->0`.

Choose anchors `o` whose mean identity-orientation error is at most `I(R)`
and gauge `q_x=R_xR_o^*`.  In the tracial/Loeb ultraproduct, `q_x` is a
reflection for almost every `x`, and `q_x,q_y` commute for an independent
uniform pair.  Put `h_t=P_tR_o^*`.  The uniform first part of `(MPC2)` says,
for every internal `t`,

```text
h_t=q_(t+alpha b) q_(t+(1+alpha)b)^* q_(t+b)                (MPC3)
```

for almost every `b`.  For fixed internal `t,s`, represent the two sides with
independent directions `b,c`.  Every cross pair between the three `b`-forms
and three `c`-forms is uniform on `K^2`; its `q`-values commute.  Swapping the
two three-letter words, without changing either word internally, proves
`[h_t,h_s]=0`.  Hence all corrected values lie in one abelian tracial von
Neumann algebra, while the second part of `(MPC2)` gives `h_t=q_t` almost
everywhere.

The corrected table is consequently a commuting-reflection table with zero
alpha-plane energy.  In a spectral representation, apply
`phased-translations-reduce-to-alpha-plane-test` fiberwise.  Its scalar
inequality extends to the hyperfinite Loeb field by approximating measurable
Boolean level sets by internal ones; translation invariance controls all four
queried vertices.  Thus the full parallelogram energy is zero.  Since `h=q`
almost everywhere and gauging preserves all three energies, a sequence with
`I+A->0` cannot keep `F` positive.

Taking the supremum of `F` over all finite tables satisfying `I+A<=delta`
defines a universal `omega(delta)->0`, proving `(NC4q)` and `(NC25)`.
