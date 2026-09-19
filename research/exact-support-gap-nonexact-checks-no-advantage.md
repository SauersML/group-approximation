---
rg: 2
id: exact-support-gap-nonexact-checks-no-advantage
kind: claim
title: Nonexact checks cannot create an exact-support mass gap absent an exact robust sub-menu
---

Let `S` be a finite relator menu, let `rho` be a fixed tracial assignment, and
write

```text
E = {r in S : rho(r)=1 exactly}.
```

For each marked finite-dimensional profile `z`, let `A_z subset S` be the
relators accepted at the enlarged defect threshold.  For any probability
measure `mu` on `S`, put

```text
g = mu(E),
q = sup_z mu(A_z).
```

If `g>q`, then **every** marked profile rejects at least one relator of `E`.
Consequently, because `E` is finite and nonempty, the uniform distribution
`nu` on `E` satisfies

```text
nu(E)=1,
sup_z nu(A_z) <= 1 - 1/|E| < 1.
```

Conversely, if some marked profile accepts every relator in `E`, then
`g<=q` for every `mu`, regardless of how much mass is put on nonexact checks.

Thus a positive exact-support mass gap cannot be manufactured by mixing in
checks that the tracial witness fails exactly.  Qualitatively it is equivalent
to having a finite exact tracial sub-menu that already rejects every marked
finite-dimensional profile.  Reweighting can optimize the margin inside `E`,
but nonexact checks provide no escape from the perfect-completeness barrier.
