---
rg: 2
id: quantitative-iwahori-projective-sign-resolution-proof
kind: route
title: Extract approximate signs, test them on relators and the edge, then use character injectivity
target: quantitative-iwahori-projective-sign-resolution
requires: []
---

For `U=rho(s)` put

```text
c_s=tr(V U V U^*) in [-1,1].
```

It is real because it is the trace of a product of selfadjoint unitaries.
Choose `epsilon_s in {+1,-1}` so that `epsilon_s c_s=|c_s|`.  Since
`U V U^*` and `V` are selfadjoint unitaries,

```text
||U V U^*-epsilon_s V||_2^2
  =2-2|c_s|
  <=2(1-|c_s|^2)
  =2 e_s
  <=a^2.                                                   (QIP1)
```

Use the same sign for `s^-1`.  Telescoping conjugations along a word
`w=s_1^{eta_1}...s_l^{eta_l}` with `eta_j in {+1,-1}` gives

```text
||rho(w)Vrho(w)^*-epsilon(w)V||_2 <= l a,                (QIP2)
```

where `epsilon(w)` is the product of the selected generator signs.

For a relator `r`,

```text
||rho(r)Vrho(r)^*-V||_2 <= 2||rho(r)-I||_2 <=2 delta.    (QIP3)
```

If `epsilon(r)=-1`, then `(QIP2)--(QIP3)` imply

```text
2=||V-(-V)||_2 <= |r|a+2delta <= L_R a+2delta,
```

contrary to `(QIS3)`.  Hence every relator has sign `+1`, so the selected
signs descend to a character

```text
chi:C->{+1,-1}.                                          (QIP4)
```

For each chosen edge word `t`, ordinary commutation with `P` gives

```text
||rho(t)Vrho(t)^*-V||_2=2||[P,rho(t)]||_2 <=2 beta.      (QIP5)
```

If `chi(t)=-1`, then `(QIP2)` and `(QIP5)` give

```text
2<=|t|a+2beta<=L_B a+2beta,
```

again contradicting `(QIS3)`.  Thus `chi|_B=1`; injectivity `(QIS1)` makes
`chi` trivial.  In particular every `epsilon_s=+1`, and `(QIP1)` yields

```text
2||[P,rho(s)]||_2
 =||rho(s)Vrho(s)^*-V||_2
 <=a.
```

Taking the maximum proves `(QIS4)`.
