---
rg: 2
id: iwahori-parent-saturated-cluster-gauge
kind: claim
title: Low-gap Iwahori clusters can be saturated so the common gauge reduces both modular vertices
---

Let `alpha_n,beta_n:K=SL_2(Z)->U(d_n)` be the two exact modular vertex
representations in a central-sector Iwahori sequence, and let their Iwahori
restrictions have irreducible isotypic projections `(P_(n,i))` and `(Q_(n,j))`.
Choose `a_n->0` with `E_n/a_n->0` as in
`mixed-intertwiner-energy-transport-localization`.

Form a graph on the disjoint union of the source and target Iwahori types with
three kinds of edges:

1. a cross edge `i--j` whenever `lambda_(n,i,j)<a_n`;
2. source-parent edges joining any two source Iwahori constituents occurring
   inside the same irreducible `K`-summand of `alpha_n`;
3. target-parent edges joining any two target constituents occurring inside
   the same irreducible `K`-summand of `beta_n`.

Let `C` run over connected components and let `P_(n,C),Q_(n,C)` be the sums of
all source/target Iwahori projections in `C`.  Then, after `o(d_n)` trivial
stabilization, there is a unitary `V_n` with `||V_n-I||_(2,d_n)->0` such that
for `beta'_n=V_n beta_n V_n^*`:

- the same orthogonal projections `R_(n,C)` reduce **both full modular
  representations** `alpha_n` and `beta'_n`;
- the source and target dimensions in each `C` agree exactly; and
- the aggregate Iwahori generator discrepancy between `alpha_n|B` and
  `beta'_n|B` still tends to zero.

Thus a putative global Iwahori basin-escape sequence splits, after negligible
stabilization and gauge, into orthogonal same-carrier subproblems whose
carriers are closed under the exact `SL_2(Z)` parent decompositions on both
sides.  The parent saturation costs no extra transport mass: it only merges
low-gap components.