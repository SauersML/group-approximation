---
rg: 2
id: level15-torsion-free-lattice-satisfies-strong-atiyah
kind: claim
title: The level-15 torsion-free lattice H in SL_3(Z) satisfies the Strong Atiyah Conjecture over C
distinct_from:
  sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts: that constructs H, proves its ranks lie in (1/2)Z and that it embeds in no torsion-free profinite group; this is integrality of its ranks.
  sl3z-satisfies-strong-atiyah: that is Strong Atiyah with denominator 24 for SL_3(Z), which implies this; this is the torsion-free test case, where only one factor of 2 is missing.
  strong-atiyah-torsion-free: that is the conjecture for every torsion-free group; this is one group, outside every recorded proof method.
---

**OPEN.** For every finite matrix `A` over `C[H]`, `rk_(N(H))(A)` is an integer. Here
`H` is the lattice of `sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts`.

- A failure is a counterexample to `strong-atiyah-torsion-free` over `C` for a
  torsion-free property (T) lattice.
- Ranks already lie in `(1/2)Z`, and the question is exactly the twisted norm
  equation `sigma(a) a = h^2` in `D_C(N)`.
