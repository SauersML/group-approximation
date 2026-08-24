---
rg: 2
id: two-tier-matricial-invisibility-proof
kind: route
title: Camouflage an MF group carrying an exact-versus-asymptotic witness
target: two-tier-matricial-invisibility
requires:
  - mf-semantic-closure-transplantation
  - bare-self-copy-mf-calibration
  - compression-defect-dies-in-finite-dimensions
---

Apply the finitely presented camouflage construction to the MF calibration
group `C` and write `pi:W->C` for its split quotient.  Since `C` is MF,
radical transplantation gives

```text
Rad_MF(W)=ker(pi)=normalClosure(d).
```

Let `z` be the copy in the `C x D` vertex of the calibration word `w=[p,a]`.
Every finite-dimensional linear representation of the Hilbert-hotel vertex
is trivial over every field, so the amalgam factorization applies to every
linear target.  It factors through `C`, whose exact representations all kill
`w`; hence every exact representation of `W` kills `z`.
In particular this applies to finite-dimensional unitary representations, so
`z` lies in both `Rad_fd(W)` and the all-fields linear residual.

On the other hand, the norm-corona detector of `w` on `C` pulls back along
`pi` and detects `z`.  Therefore `z` is outside `Rad_MF(W)`.  Finite targets
embed in finite-dimensional linear groups, and Peter--Weyl point separation
shows that the same exact invisibility holds for every compact target.
Finally `C` maps onto `Z^2` through the classes of `t` and `p`, so their
copies in `W` are already visible in one-dimensional exact representations.
Finite presentability is inherited from the finite amalgam presentation.
