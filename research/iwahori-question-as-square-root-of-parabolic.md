---
rg: 2
id: iwahori-question-as-square-root-of-parabolic
kind: claim
title: The Iwahori amalgam is two copies of C2 star C3 glued by a parabolic square root
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - experiments/psl2_half_exotic_search.py
  - experiments/psl2_half_exotic_torch.py
  - experiments/psl2-half-square-root-sanity.json
distinct_from:
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich's question in representation-variety language; this is an explicit finite presentation and an equivalent square-root formulation of the same question.
---

Write `PSL_2(Z)=C_2*C_3=<x,y | x^2,y^3>` with `x=S`, `y=ST`, so the
parabolic is `T=xy`.  Let `t=diag(2,1)`, `V_1=PSL_2(Z)`,
`V_2=t^(-1)V_1t`, and

```text
B=V_1 cap V_2=Gamma_0(2)/+-=<T,eps>,
eps=x y^2 x y x.
```

Then

```text
PSL_2(Z[1/2]) = < x,y,x',y' | x^2=y^3=x'^2=y'^3=1,
                                  xy=(x'y')^2,
                                  xy^2xyx=x'y'x'y'^2x' >.       (SR1)
```

Here `x'=t^(-1)xt`, `y'=t^(-1)yt`; hence `T'=x'y'` is translation by
`1/2` and `T=(T')^2`.  Swapping the vertex copies gives the mirror
orientation.

**Square-root form.**  Given a representation `(x,y)` of `C_2*C_3`, put

```text
T=xy,             eps=xy^2xyx.
```

A second vertex representation extending it across the edge is equivalent
to a square root `s` of `T` satisfying

```text
s^2=T,                  (eps s)^3=1.                    (SR2)
```

Indeed, with `s=x'y'`, the second edge word is `eps=s x' s^(-1)`.  Thus

```text
x'=s^(-1)eps s,          y'=x's=s^(-1)eps T.
```

The involution relation for `x'` is automatic, and conjugating `y'` by `s`
gives `eps s`; hence `y'^3=1` is exactly the second relation in `(SR2)`.
Conversely these formulas reconstruct the second vertex and both edge
identifications.

This makes the global stability problem concrete: an approximate
representation is an exact or rounded modular vertex together with an
approximate square root of its parabolic satisfying one cubic compatibility
word.  Congruence representations provide canonical roots because their
parabolic images have finite odd order.

**Sanity.**  The bounded Torch sanity run gives zero for both gluing defects
and all four torsion defects on `P^1(F_p)` for `p=5,7,11`; the checked
parabolic orders are respectively `5,7,11`.
