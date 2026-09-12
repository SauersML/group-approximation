---
rg: 2
id: effective-corner-support-higman-proof
kind: route
title: Enumerate the support-subgroup relations and Higman embed
target: effective-corner-host-higman-promotion
requires:
  - finite-support-corner-localizes-obstruction
  - higman-bypass-needs-only-fg-recursive-nonhyperlinear
---

Form the finite support subgroup `Lambda` as in
`finite-support-corner-localizes-obstruction`.  It is nonhyperlinear.  Fix
words `w_1,...,w_m` in the recursive generators of `Gamma` representing its
finite generating set.  Enumerate the normal closure of the recursive
relators of `Gamma`.  Whenever this enumeration proves

```text
W(w_1,...,w_m)=1 in Gamma
```

for a word `W` in `m` letters, enumerate `W` as a relator of `Lambda`.
Conversely every relation of `Lambda` is eventually found, so this is a
recursive presentation of `Lambda`.  Apply the established effective Higman
embedding.  Its finitely presented output contains the nonhyperlinear group
`Lambda`, and therefore cannot be hyperlinear.

