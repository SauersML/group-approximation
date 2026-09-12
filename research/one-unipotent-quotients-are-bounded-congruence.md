---
rg: 2
id: one-unipotent-quotients-are-bounded-congruence
kind: claim
title: A one-unipotent Iwahori quotient differs from PSL2 modulo N by only the fixed congruence kernel
distinct_from:
  bounded-period-iwahori-quotients-are-finite: that uses only the normal-subgroup theorem to prove finiteness; this identifies the finite quotient up to a kernel of uniformly bounded order.
  finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence: that classifies one representation through an unspecified odd level; this identifies the whole universal quotient obtained by killing one unipotent power.
  fixed-level-bs14-compatible-basin: that asks for a quantitative HS repair modulus as the level moves; this removes abstract finite-group structure from that question but does not prove the modulus.
---

Put

```text
Gamma=PSL_2(Z[1/2]),
s=[[1,1/2],[0,1]],
Q_N=Gamma/<<s^N>>                         (BCE1)
```

for an odd integer `N`.  Let `C_cong` be the finite congruence kernel of
`Gamma`, and put `c_Gamma=|C_cong|`.  Reduction modulo `N` induces an exact
sequence

```text
1 -> E_N -> Q_N -> PSL_2(Z/N) -> 1,       (BCE2)
|E_N| <= c_Gamma.                         (BCE3)
```

Thus the one-power targets in the bounded-cycle staircase are uniformly
bounded extensions of their expected odd congruence quotients.  In
particular there are constants `a_Gamma,b_Gamma>0`, independent of odd `N`,
such that

```text
a_Gamma N^3 <= |Q_N| <= b_Gamma N^3.      (BCE4)
```

This sharpens the fixed-level finiteness theorem in the only direction that
abstract finite-group structure permits.  The moving basin is now a uniform
normalized-HS stability problem for the congruence family
`PSL_2(Z/N)`, up to one fixed finite kernel.  It is not a problem caused by
uncontrolled exotic finite quotients.  Conversely, `(BCE2)` supplies no
quantitative presentation-stability radius: congruence classification of
exact representations begins only after an approximate tuple has been
corrected.
