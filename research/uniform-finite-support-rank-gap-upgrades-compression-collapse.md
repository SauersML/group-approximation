---
rg: 2
id: uniform-finite-support-rank-gap-upgrades-compression-collapse
kind: claim
title: A uniform finite-subgroup support bound upgrades compression-defect collapse to operator norm
distinct_from:
  locally-finite-defect-subgroup-dies-in-every-corona: that asks for all locally finite normal subgroups without a support-rank hypothesis; this proves the theorem when one torsion mark uniformly controls every finite stage.
  torsion-normal-generator-mf-shadow-equivalence: that requires finite normal-generation data for the whole ambient group; this allows a proper locally finite normal subgroup and a nontrivial ambient quotient.
artifacts:
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
---

Let G be countable, H<=G have property (T), and A=union_j A_j be a
locally finite normal subgroup with an increasing finite exhaustion.
Fix a in A_1 of finite order m>=2. Suppose C<infinity satisfies

    dim((Fix sigma(A_j))^perp)<=C rank(sigma(a)-I)

for every finite-dimensional unitary representation sigma of every
A_j. If a lies in the compression defect D_G(H), then a belongs to
Rad_MF(G).

The proof uses positive finite-rank cutoffs and one-sided transport
in the Hilbert norms (Tr/rank(sigma(a)-I))^(1/2). It does not need
operator-norm compression of the ambient group to a projection,
extension of an MF trace, or property (T) for A. Local finiteness
without the displayed uniform bound remains outside the theorem.
