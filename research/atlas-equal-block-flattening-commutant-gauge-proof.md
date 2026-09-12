---
rg: 2
id: atlas-equal-block-flattening-commutant-gauge-proof
kind: route
title: Controlled right translations flatten every block inside one chart gauge orbit
target: atlas-equal-block-flattening-is-commutant-gauge
requires:
  - atlas-true-criterion-baseline
---

Let `A` have order `m`.  On `H=l2(A)` use conventions under which `L_g`
and `R_a` commute.  On the extra multiplicity space `E=l2(A)`, let
`p_a=|delta_a><delta_a|` and define

```text
C=sum_a R_a tensor I_k tensor p_a.                       (P1)
```

The summands in `(P1)` have orthogonal initial and final `E`-supports, so

```text
C C*=C* C=sum_a I_H tensor I_k tensor p_a=I.             (P2)
```

Also `[C,L_g tensor I_k tensor I_E]=0` for every `g`, because left and
right regular translations commute.  For

```text
U_hat=(U tensor I_E)C                                    (P3)
```

we consequently have

```text
U_hat(L_g tensor I_(k m))U_hat*
 =(U(L_g tensor I_k)U*) tensor I_E.                      (P4)
```

The first chart is itself amplified by `I_E`.  Evaluation of any word in
the two chart factors therefore changes from `pi_U(w)` to
`pi_U(w) tensor I_E`.  Normalized traces and normalized `2`-norms are
unchanged, proving the chart and relator assertions.

It remains to compute the blocks.  For fixed `y,z in A`, exactly one `a`
satisfies `R_a delta_y=delta_z`; denote it by `alpha(z,y)`.  Hence

```text
C_(z,y)=I_k tensor p_(alpha(z,y)),
(U_hat)_(x,y)=sum_z U_(x,z) tensor p_(alpha(z,y)).        (P5)
```

For fixed `y`, the map `z |-> alpha(z,y)` is a bijection.  The summands in
the second formula of `(P5)` thus have orthogonal `E`-supports, and

```text
||(U_hat)_(x,y)||_HS^2
 =sum_z Tr(U_(x,z)* U_(x,z))
 =Tr(sum_z U_(x,z) U_(x,z)*)
 =Tr(I_k)=k.                                             (P6)
```

The middle equality uses equality of the two finite traces; the last uses
the `(x,x)` block of `U U*=I`.  This proves equal block norms.

Finally take `k=1` and `U=J`, where `J` implements inversion and sends the
left regular chart to the right regular chart (up to the harmless inverse
convention).  Multiplication by `J` merely permutes the output block index in
`(P5)`, so every block becomes one of the rank-one projections `p_a`, with
each `p_a` appearing exactly once in every row and column.  This is the
claimed magic/quantum-Latin block form.  Equation `(P4)` says its represented
second chart is still right regular.  The exact tensor-flip evaluation in
`atlas-true-criterion-baseline` therefore applies unchanged: cartesian
controls have zero defect and each single-factor escapee has defect
`sqrt(2)`.  This completes the proof.
