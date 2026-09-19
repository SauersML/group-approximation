---
rg: 2
id: torsion-free-countable-non-mf-from-fp-witness
kind: route
title: The established finitely presented witness is already countable and recursively presented
target: torsion-free-countable-non-mf
requires: [torsion-free-finitely-presented-non-mf]
---

## Why sufficient

The root `torsion-free-finitely-presented-non-mf` is established, by
`torsion-free-non-mf-from-normal-kazhdan-defect`, at the Fournier-Facio group
`G`.  A finitely presented group is countable and is recursively presented,
so `G` witnesses this claim as stated, including its parenthetical
preference.  No analytic step, no embedding, and no heredity lemma is
consumed: the target is the strictly weaker existence statement and the
witness is the same group.

## This closes the loop the claim was written to open

The claim exists because dropping finite presentation looked like the cheap
half of the root: `mf-positive-controls` sends non-MF-ness **up** to
overgroups, so a torsion-free countable non-MF group plus a torsion-free
Higman embedding gives the root
(`torsion-free-fp-from-countable-witness`).  That was the useful direction
while the root was open.  With the root established the traffic reverses, and
the two routes together are the kernel's equivalence — two routes, one each
way, which is what an equivalence *is* here and never a defect.  `cairn
check` reports dependency cycles only for rings of three or more claims, so
this two-claim ring is silent by design; it is recorded here so that nobody
reading the pair later mistakes it for circular reasoning.

Note the asymmetry that survives.  This direction is unconditional.  The
reverse direction still carries `torsion-free-higman-embedding`, which is
unverified, so it remains the route to repair if a *different* torsion-free
countable non-MF group ever needs promoting to a finitely presented one.
