---
rg: 2
id: stw95-nonexact-excess-kernel-obstructs-purity
kind: claim
title: A nonpure tensor-exactness excess kernel refutes pure-tensor permanence
distinct_from:
  entangled-compact-image-obstructs-tensor-purity: that requires an elementary compact-bearing representation image; the excess kernel here may be nowhere scattered and fail either Cu regularity axiom.
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
---

Let `A,B` be pure C*-algebras and `I` a closed ideal of `A`.  Set

```text
K = ker(A tensor_min B -> (A/I) tensor_min B),
E = K/(I tensor_min B).
```

If `E` is not pure, then `A tensor_min B` is not pure.  Necessarily `B` is
nonexact on this extension; if `B` is exact then `E=0`.
