---
rg: 2
id: finitary-linear-extension-sofic-and-no-finite-normal-subgroup
kind: claim
title: Finitary linear extensions are sofic, finitely generated and free of finite normal subgroups, with a simple kernel
distinct_from:
  dyadic-perturbation-group-is-sofic: that proves soficity of one concrete finitary PERMUTATION group over the dyadic base; this is the permanence package for finitary LINEAR extensions over an arbitrary base action, and also supplies finite generation, the absence of finite normal subgroups, and simplicity of the kernel.
  finitary-linear-extension-kazhdan-defect-kills-kernel: that is the non-MF half of this family and explicitly declines a soficity claim; this carries no Kazhdan hypothesis at all and proves the structural half instead.
  compression-action-theorem-for-finitary-linear-extensions: that is the non-MF theorem and needs a compressed Kazhdan subgroup with a moved forward point; this holds for the same semidirect product independently of any such hypothesis.
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

**ESTABLISHED.** Let a countable `V` act on a countably infinite `X`,
`K = GL_fin(F_2^(X))`, `G = K x| V`.

**Soficity.** If `N` is normal in `V` and sofic, `V/N` is amenable,
and every finitely generated subgroup of `N` has finite orbits on `X`,
then `G` is sofic.

**Finite normal subgroups.** If every nonidentity element of `V` moves
infinitely many points, `G` has no nontrivial finite normal subgroup.

**Finite generation.** If `V` is finitely generated and transitive on
`X`, then `G` is finitely generated.

**The kernel.** `K` is an infinite, locally finite, **simple** group,
being the directed union of the `GL_n(F_2)`.

The three hypotheses are independent of each other and of any Kazhdan
input, so this claim is the structural companion to the non-MF theorem
rather than part of it.

DERIVATION
finitary-linear-permanence-proof
