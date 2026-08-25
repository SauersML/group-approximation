---
rg: 2
id: spectator-dilution-hides-root-profile-from-hs-correction
kind: claim
title: Spectator dilution hides a quasiregular root profile from every global Hilbert--Schmidt correction
distinct_from:
  canonical-trace-does-not-weaken-thin-commutant-transfer: that tensors an actor model with separating finite regular quotients while preserving a selected unitary commutator; this dilutes an arbitrary distinguished-vector coefficient into a vanishing-dimensional summand and makes the whole unitary model close to the trivial exact representation.
  tensor-root-profile-adds-no-chart-coherence: that proves scalar tensor powers add no label coordinates; this proves normalized-HS correction can erase the entire carrier of the selected coefficient at negligible cost.
---

Suppose finite-dimensional asymptotic representations `beta_n` on `K_n`
and unit vectors `xi_n` have any prescribed limiting coefficient `phi`.
Choose `m_n/dim(K_n)->infinity` and put

```text
beta'_n(g)=beta_n(g) direct_sum 1_(m_n),
xi'_n=xi_n direct_sum 0.                               (SDH1)
```

Then the distinguished coefficients are unchanged:

```text
<beta'_n(g)xi'_n,xi'_n>=<beta_n(g)xi_n,xi_n>.          (SDH2)
```

But, with normalized Hilbert--Schmidt norm on the enlarged space,

```text
||beta'_n(g)-1||_2
 <=2 sqrt(dim(K_n)/(dim(K_n)+m_n)) ->0                 (SDH3)
```

for every fixed `g`.  Thus the whole model is asymptotically HS-close to the
exact trivial representation even when `phi=1_H` for a proper subgroup
`H<A`.

Consequently property `(T)`, flexible HS correction, or any global
normalized-HS exactification statement does not by itself control the
distinguished root coefficient after the tensor-amplification reduction:
the correcting perturbation may erase precisely the vanishing-dimensional
summand containing `xi'_n`.  Promotion to a sofic atlas needs a
positive-density selected-vector/chart condition, not merely correction of
the ambient matrices.
