---
rg: 2
id: kt-finitary-action-is-outer-mod-scalar-core
kind: claim
title: The full Kun--Thom finitary-factor action is outer modulo its explicit scalar core
distinct_from:
  wreath-candidate-embeds-in-finitary-permutation-extension: that proves an infinite-support permutation induces an outer automorphism of the finitary symmetric factor, conditional on infinite support; this computes exactly which elements of the full Kun--Thom actor have finite support.
  kun-thom-finitary-action-lifts-to-normalizer: that asks for a homomorphic normalizer lift of the action; this removes the trace bookkeeping by proving outerity after the harmless specialization `q=2`, but does not split the full pullback cocycle.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: that identifies the binary-lamp orbit of the external `SL_3(Z)` factor; this treats the action on the entire coset set and the induced automorphisms of the full finitary symmetric factor.
---

For the Kun--Thom Theorem E pair write

```text
Gamma=EL_r(F_q[x_1,x_2,x_3]),
G=EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z),
X=G/Gamma,                    Y=X x {0,1}.
```

Let `alpha` be the induced action on
`R=L(Sym_fin(Y))`.  The kernel of the permutation action on `X`, and hence
the set of actor elements whose permutation has finite support, is exactly

```text
Z_0={zeta I_r : zeta in F_q^*, zeta^r=1}.              (OUT1)
```

Every `g notin Z_0` moves infinitely many points of `X`, and

```text
alpha_g is outer                  (g notin Z_0).        (OUT2)
```

The elements of `Z_0` act trivially.  In particular, for the valid
specialization `q=2`, one has `Z_0={1}` and the action of **every**
nonidentity element of the full actor `G` on `R` is outer.  Therefore the
trace condition `(KFL1)` in
`kun-thom-finitary-action-lifts-to-normalizer` is automatic at `q=2`; its
only remaining content is splitting the pullback normalizer extension.

This also corrects the overbroad informal assertion that every nonidentity
Laurent elementary element has infinite support for arbitrary `q`: the only
exceptions are the displayed constant scalar center, and they disappear
over `F_2`.
