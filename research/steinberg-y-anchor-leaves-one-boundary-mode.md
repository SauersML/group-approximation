---
rg: 2
id: steinberg-y-anchor-leaves-one-boundary-mode
kind: claim
title: The exceptional Y anchor leaves exactly one projective boundary mode
artifacts:
  - research/steinberg-y-boundary-mode-proof.md
distinct_from:
  steinberg-fox-recurrence-forces-zero-marginals: this is a scoped obstruction to proving marginal vanishing from the exceptional Y orbit alone, not a counterexample to the full two-row marginal system.
---

**ESTABLISHED FIREWALL.**  Without assuming zero marginals, the `Y` row
on the exceptional fiber `a=-1/2,b=0` forces

```text
f(-1/4,0,0)=0,
f(-1/4,0,t)=kappa       for every t!=0,
P(-1/4,0)=-kappa.                                      (SYB1)
```

Thus projective `r`-propagation leaves one scalar boundary mode.  The
pushed `Y`-plane equation at `c=0` and the pointwise `Y` equation on
`(a,0,0)` are identities, so neither can kill `kappa`.  For `p>=5`, the
`X` row on this pencil exports `kappa` into one `q`-difference pencil and
one transverse `s`-difference pencil; it does not annihilate it locally.
Any proof of marginal vanishing must control that coupled cascade.

DERIVATION
steinberg-y-boundary-mode-proof
