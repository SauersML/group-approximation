---
rg: 2
id: mf-safe-finite-presentation-compiler-via-mikhailova
kind: route
title: Compile the recursive kernel with a Mikhailova witness and tensor-synchronize the rope
target: mf-safe-finite-presentation-compiler
requires:
  - mikhailova-fiber-product-gives-regular-mf-benign-compiler
  - mf-safe-asymmetric-hnn-replacement
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
---

Apply the regular-MF Mikhailova benign compiler to the recursively enumerable
kernel `N_e normal F` of the three-generator bridge.  This gives, uniformly and
without testing the branch, a finitely presented residually finite ambient
group `K_e^0`, an embedded `F`, and a finitely generated cutting subgroup
whose intersection with `F` is exactly `N_e`.

Take its product/intersection with the fixed finite-CEP graph witness for the
positive kernel `N_+`.  Since `N_e<=N_+`, the product still cuts out `N_e`.
The first central rope HNN is regularly operator-MF because its base is.  On
`INF`, the graph factor supplies the finite edge maps and the tensor-sync
theorem handles the final graph-valued HNN edge.  On `FIN`, the same benign
intersection and Britton normal form embed the bridge group containing `E`.
Every presentation and marked generating set is finite and computed uniformly.
