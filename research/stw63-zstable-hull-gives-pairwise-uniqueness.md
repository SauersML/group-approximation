---
rg: 2
id: stw63-zstable-hull-gives-pairwise-uniqueness
kind: claim
title: A unital Z-stable hull of two Jiang--Su ranges gives pairwise uniqueness
distinct_from:
  stw63-every-z-pair-has-joint-central-bridge: that asks for a bridge for every pair in every codomain; this proves the bridge when only the subalgebra surrounding the chosen pair is Z-stable.
---

Let `B` be unital and let `phi,psi:Z->B` be unital embeddings.  If there is a
unital `Z`-stable C\*-subalgebra `C subset B` containing both ranges, then
`phi` and `psi` are approximately unitarily equivalent in `B`.

In particular this applies when the pair-generated algebra

```text
C*(phi(Z) union psi(Z))
```

is `Z`-stable.  Hence any counterexample to LXIII generates no unital
`Z`-stable hull inside its codomain.
