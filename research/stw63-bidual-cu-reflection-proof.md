---
rg: 2
id: stw63-bidual-cu-reflection-proof
kind: route
title: Reflect equality of bidual Cu maps and apply Robert
target: stw63-sr1-bidual-cu-reflection-return
requires:
  - stw63-all-von-neumann-codomains-have-uniqueness
  - stw63-sr1-return-is-cu-equality
---

Let `phi,psi:Z->B`.  Universal von Neumann uniqueness makes `i phi` and
`i psi` approximately unitarily equivalent in `B**`.  Functoriality and
invariance of `Cu` under approximate unitary equivalence give

```text
Cu(i) Cu(phi) = Cu(i phi) = Cu(i psi) = Cu(i) Cu(psi).   (2)
```

If (1) is injective, (2) implies `Cu(phi)=Cu(psi)`, and the exact
stable-rank-one return theorem gives approximate unitary equivalence in `B`.

Conversely, if the pair is inequivalent, Robert's theorem says that its two
`Cu` maps differ at some `x in Cu(Z)`, while (2) says their values become
equal under `Cu(i)`.  These two values are the promised explicit witness to
failure of injectivity.  The converse statement does not claim that an
arbitrary kernel pair for `Cu(i)` is realized by Jiang--Su embeddings.
