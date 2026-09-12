---
rg: 2
id: graph-endomorphism-phase-hnn-embeds-formanek-procesi
kind: claim
title: Every injectively distorted phase-duplication HNN embeds in the Formanek-Procesi group
distinct_from:
  diagonal-hnn-exactly-advances-free-phase-depth: that uses the identity map in the second phase factor; this permits an arbitrary injective endomorphism of the free support group.
  ascending-hnn-cannot-create-nonhyperlinearity: that applies an endomorphism to the whole base; this HNN identifies one proper direct factor with the graph of the endomorphism inside two commuting factors.
---

Let `L` be a finite-rank free group and let `theta:L -> L` be injective.  Put

```text
E_theta=<L_0 times L_1,t |
 t(g,1)t^(-1)=(g,theta(g)), g in L>.                     (GEH1)
```

This edge map exactly sends a one-layer phase coefficient `w in L_0` to the
distorted two-layer coefficient `(w,theta(w))`.  In particular, for the
matrix-coefficient embedding `(FPS3)`, conjugation by `t` sends

```text
E_(ij) a_i^(0)(a_j^(0))^(-1)
```

to the product of that coefficient with
`theta(a_i)^(1)theta(a_j)^(-1)^(1)`.

Nevertheless `E_theta` embeds in the reverse-orientation Formanek--Procesi
group

```text
H^+(L)=<L_0 times L_1,u | u(g,1)u^(-1)=(g,g)>.           (GEH2)
```

The embedding is

```text
(g,h) |-> (theta(g),h),                 t |-> u.          (GEH3)
```

Therefore `E_theta` is residually finite and hyperlinear by
`formanek-procesi-diagonal-hnn-is-residually-finite`.

Thus no injective substitution applied independently to the second commuting
phase copy can be the decisive signed-Hecke chord.  A live asymmetric edge
must fail to factor as the graph of one injective endomorphism in this way.
