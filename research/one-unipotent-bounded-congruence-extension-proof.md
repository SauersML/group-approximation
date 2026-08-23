---
rg: 2
id: one-unipotent-bounded-congruence-extension-proof
kind: route
title: Compute the closed local normal closures and pull back through the finite congruence kernel
target: one-unipotent-iwahori-quotients-are-bounded-congruence-extensions
requires:
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

Serre's congruence subgroup theorem gives a surjection

```text
hat(Gamma) -> product_(p odd) PSL_2(Z_p)               (BCP1)
```

with finite kernel `C_cong`.  Strong approximation identifies the target
with the congruence completion.  The image of `s^N` in the `p`-factor is
the elementary unipotent

```text
u(N/2)=[[1,N/2],[0,1]].                                (BCP2)
```

We first compute its closed normal closure locally.  If `a=v_p(N)`, then
the closed normal closure of `u(N/2)` in `PSL_2(Z_p)` is the principal
congruence kernel of level `p^a` (with level `p^0` interpreted as the whole
group).  Indeed integer powers, followed by closure, give every upper
unipotent `u(p^a z)`, `z in Z_p`; Weyl conjugacy gives all lower
unipotents of the same level.  These root groups normally generate the
principal congruence kernel.  When `a=0`, their reductions normally
generate `PSL_2(F_p)` (also for `p=3`), and the same root-group argument
contains the full pro-`p` kernel, so the closed normal closure is the whole
local group.

Conjugators may be chosen independently in the factors of `(BCP1)`.
Consequently the closed normal closure of the image of `s^N` in the whole
congruence completion is

```text
K(N)=ker(product_(p odd) PSL_2(Z_p) -> PSL_2(Z/N)).    (BCP3)
```

Let `L_N` be the closed normal closure of `s^N` in `hat(Gamma)`.  Pulling
`(BCP3)` back through `(BCP1)` gives

```text
ker(hat(Gamma)/L_N -> PSL_2(Z/N))
   = C_cong L_N/L_N,
```

which is a quotient of `C_cong`.  The abstract normal closure `<<s^N>>`
has finite index by the S-arithmetic normal-subgroup theorem.  It is
therefore closed in the profinite topology, and the natural finite quotient
`Q_N` is exactly `hat(Gamma)/L_N`.  This proves `(BCE2)--(BCE3)`.

Reduction is surjective: `s` supplies an upper elementary generator because
`2` is invertible modulo odd `N`, and the Weyl element supplies the lower
one; elementary matrices generate `SL_2(Z/N)`.  Finally

```text
|SL_2(Z/N)|=N^3 product_(p|N)(1-p^(-2)).               (BCP4)
```

Passing to the projective quotient changes this by a factor at most two.
Since `product_p(1-p^(-2))=1/zeta(2)>0`, `(BCE2)--(BCE3)` and `(BCP4)`
give `(BCE4)`.

