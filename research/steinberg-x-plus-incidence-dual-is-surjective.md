---
rg: 2
id: steinberg-x-plus-incidence-dual-is-surjective
kind: claim
title: The X-adjoint image plus endpoint potentials spans every chord function
---

Let `D(f)=(P_f,H_f)` be the biaffine endpoint map and let `X_ch` be the
first chord Fox row with its tree-cut substitutions.  Then

```text
im(X_ch^*)+im(D^*)=F_p^(F_p^3).                        (SXD1)
```

Explicitly,

```text
D^*(alpha,beta)(a,b,c)=alpha(a,b)+beta(c,ac-b),
X_ch^*=(1-q^(-1))A^(-1)+(1-s^(-1))B^(-1)-1,          (SXD2)
```

where the group elements act on the Steinberg chord model, including the
fixed tree-cut extension.  This is equivalent to

```text
ker(X_ch) intersect ker(P,H)=0.                        (SXD3)
```

It is stronger than the currently needed two-row zero-marginal claim.  The
support split and matching-zero firewall do not prove it: they leave the
derivative compatibility of the two punctured circulations unresolved.
