---
rg: 2
id: non-hyperlinear-from-e3-fibre-llp
kind: route
title: LLP of all three mod-three fibres makes the Deligne triple cover a non-hyperlinear witness
target: non-hyperlinear-group
requires:
  - sp2g-z-full-c-star-algebra-has-llp
  - sp4-mod3-twisted-fibres-have-llp
  - llp-non-rf-kazhdan-group-is-non-hyperlinear
  - deligne-triple-cover-fd-central-invisibility
---

`E_3` is finitely presented (finite central extension of the finitely
presented `Sp_4(Z)`), has property (T) (finite central extension of a
Kazhdan group), and is not residually finite: by
`deligne-triple-cover-fd-central-invisibility` every finite-dimensional
unitary representation of `E_3` kills the central `z`, so every finite
quotient does, and `z != e` survives in no finite quotient.

The finite central `Z/3` gives three central idempotents
`p_j = (1/3) sum_k omega^(-jk) z^k` in `C^*(E_3)`, decomposing

```text
C^*(E_3) = C^*(Sp_4(Z)) (+) C^*(Sp_4(Z); alpha) (+) C^*(Sp_4(Z); alpha^2).
```

A finite direct sum has the LLP iff each summand does (summands are ccp
retracts, and lifts assemble blockwise), so the two required LLP claims
give the LLP for `C^*(E_3)`.  Now
`llp-non-rf-kazhdan-group-is-non-hyperlinear` applies verbatim to the
non-residually-finite Kazhdan group `E_3`: it is not hyperlinear.  The
witness is the explicit finitely presented arithmetic-flavoured group
`E_3`, and by `deligne-sector-gap-is-exactly-nonhyperlinearity` the
conclusion is equivalent to the Deligne lane's mod-three Maslov defect
gap, so this route and that lane certify each other's endpoint.

**Fence status.**  A torsion-free fenced subgroup of `E_3` meets the
central `Z/3` trivially and embeds into `Sp_4(Z)`, so the `g = 2`
subgroup audit of `sp2g-z-full-c-star-algebra-has-llp` covers this route
as well; no known LLP-failure group is recorded inside `E_3`.
