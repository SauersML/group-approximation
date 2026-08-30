---
rg: 2
id: stw99-lxxvi-ideal-local-k0-protection-proof
kind: route
title: Keep the partial isometry in the generated ideal and use the KK-equivalence C to Z
target: stw99-lxxvi-ideal-local-k0-protection
requires: []
---

Assume for contradiction that the two displayed classes agree after
tensoring with Z.  Cuntz equivalence of projections is stable
Murray--von Neumann equivalence, so in a further matrix stabilization there
is a partial isometry `v` with

```text
v* v = p tensor 1_Z,       v v* = q tensor 1_Z.
```

The algebra `J tensor_min Z` is an ideal of
`(A tensor K) tensor_min Z` because Z is nuclear.  Moreover

```text
v = (q tensor 1_Z) v (p tensor 1_Z),
```

so `v` lies in the stabilization of `J tensor_min Z`.  Hence

```text
[p tensor 1_Z] = [q tensor 1_Z] in K_0(J tensor_min Z).
```

The unital inclusion `C -> Z` is a KK-equivalence.  Exterior product with
`J` therefore makes the first-factor inclusion

```text
J -> J tensor_min Z
```

a KK-equivalence, and in particular an isomorphism on `K_0`.  Injectivity
then gives `[p]=[q]` in `K_0(J)`, a contradiction.
