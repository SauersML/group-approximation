---
rg: 2
id: graph-witness-product-proof
kind: route
title: Intersect the two witnesses and let their factors perform separate jobs
target: graph-witness-product-supplies-tensor-sync
requires:
  - finite-cep-kernel-witness-synchronizes-rope
  - regular-mf-tensor-sync-proves-twisted-rope-mf
  - regular-mf-central-hnn-closure
---

The direct-product benign construction intersects the two cut-out subgroups,
giving `(GWP2)`.  On the positive branch, direct products preserve regular
MF realizations and the cited central-HNN theorem handles the first rope
letter.  In every requested finite model, kill the ordinary witness factor
and use the graph factor's diagonal/swap map.  Its restriction to the rope
subgroup has kernel contained in the requested fold kernel.  The tensor-sync
theorem supplies faithfulness from the regular model of the whole first rope
group and compatibility from that finite graph map.
