---
rg: 2
id: recursive-permutational-lamp-presentation-proof
kind: route
title: Enumerate stabilizer identifications and commuting lamp conjugates
target: recursive-permutational-lamp-presentation
requires: []
---

Write the actor as `A=<S|R>` with finite `S` and recursively enumerable `R`,
and choose a basepoint lamp `c`. Enumerate the relators

```text
R,  c^2=1,  [c,h]=1  (h in the r.e. stabilizer preimage),
[c,g c g^-1]=1       (g in F(S)).
```

Every family is recursively enumerable. The stabilizer relators identify two
conjugate lamps exactly when their actor words name the same point, while the
last family makes all site lamps commute. Hence the presented normal closure
of `c` is the direct sum of one `C_2` per orbit point, and conjugation by `S`
is the given permutation action. Transitivity makes `S union {c}` finite and
generating, so this is the required recursive presentation.

For a conjugacy-class action of an involution `i`, enumerate the stabilizer
preimage by enumerating formal proofs of `[h,i]=1`; no word-problem decision
procedure or finite generation of the centralizer is needed.
