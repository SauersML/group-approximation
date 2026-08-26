---
rg: 2
id: property-t-free-torsion-free-full-mf-radical
kind: claim
title: Produce the manuscript's torsion-free full-MF-radical group without Property T
root: true
distinct_from:
  defect-saturation-full-mf-radical: that proves the printed torsion-free theorem by putting a normal Kazhdan subgroup inside the compression defect; this asks for the same non-Kazhdan conclusions with no Property-T or Kazhdan dependency anywhere in the proof.
  torsion-free-finitely-presented-non-mf: that asks only for one torsion-free finitely presented non-MF group and is currently proved by a Kazhdan route; this retains the stronger two-generator, acylindrically hyperbolic, full-radical, and quotient-hereditary conclusions printed in the manuscript.
---

**OPEN.**  Construct a two-generated, finitely presented, torsion-free,
acylindrically hyperbolic group `Q` such that

```text
Rad_MF(Q)=Q,
```

and every nontrivial quotient of `Q` again equals its full MF radical.  The
construction and proof may not invoke Property `(T)`, a Kazhdan subgroup,
a Kazhdan projection, or Kazhdan transport.

This is the exact no-Property-`(T)` replacement for the manuscript's second
main theorem after deleting its explicit assertion that `Q` has Property
`(T)`.  It is independent of the binary-Leavitt EL20 collapse: the printed
Hull saturation starts from a torsion-free Kazhdan compression group, while
the binary-Leavitt seed contains involutions and cannot embed in a
torsion-free group.

The algebraic saturation step itself is reusable.  If a finitely presented
torsion-free acylindrically hyperbolic group `G_0` contains a nonzero normal
subgroup `N<=Rad_MF(G_0)`, Hull saturation can force the image of `N` to
normally generate a two-generated torsion-free quotient; MF-radical
functoriality then makes that quotient full radical, and the same argument
applies to every nontrivial quotient.  The missing no-`(T)` input is therefore
such a torsion-free `G_0,N` pair together with a proof of `N<=Rad_MF(G_0)`.

The existing `defect-saturation-full-mf-radical` does not supply this input:
its radical inclusion is exactly the normal-Kazhdan theorem.
