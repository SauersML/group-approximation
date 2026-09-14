---
rg: 2
id: normal-subgroups-of-arithmetic-lattices-are-congruence-open
kind: claim
title: A nontrivial normal subgroup of a torsion-free arithmetic group has open closure in the congruence completion
distinct_from:
  hyperbolic-rf-question-reduces-to-one-fixed-host: that reduces Gromov's question to quotients of a fixed host using Olshanskii's theorem; this is an arithmetic fact about which finite quotients those quotients can have when the host is an arithmetic lattice
---

Let `k` be a number field with ring of integers `O`, let `G` be a simply
connected absolutely almost simple `k`-group with `G(k_v)` noncompact for some
archimedean place `v`, and let `Γ <= G(O)` be torsion-free of finite index.
Let `Γ̄` be the closure of `Γ` in `G(Ô) = ∏_𝔭 G(O_𝔭)`.

If `1 != M ⊴ Γ`, then the closure of `M` in `Γ̄` is open.  Consequently
`Γ/M` has only finitely many congruence quotients: all of them factor through
the finite group `Γ̄ / closure(M)`.

For `G(k_v) = Sp(2,1)` this applies to torsion-free cocompact arithmetic
lattices, and so to every quotient `Γ/M` of such a lattice: its residual
finiteness, if it holds, is carried by **non-congruence** finite quotients of
`Γ` alone.

Proof in `arithmetic-normal-subgroup-congruence-openness-proof`.  No novelty
claimed.  Not Lean-verified.
