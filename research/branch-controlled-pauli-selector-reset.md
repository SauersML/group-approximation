---
rg: 2
id: branch-controlled-pauli-selector-reset
kind: claim
title: Two raw-branch-controlled Pauli families balance an abelian selector chart
distinct_from:
  nested-schur-multiplicity-wire-globalizes-selectors: that rules out putting the next packet directly in the old selector commutant; this supplies a finite transverse factor which removes that center first.
  controlled-central-phase-finite-group-barrier: that rules out using a nonlinear selector predicate as a central phase; this uses only the genuine Schur child bit `q` and its complement `Jq`.
---

Let `D=<J,q,z_1,...,z_k>` be an elementary abelian subgroup of a packet and
work on the marked sector `J=-1`. The elements `J,z_i` may be central in the
packet; `q` is required only to commute inside `D`. Adjoin involutions

```text
s_i^-, s_i^+       (1<=i<=k)
```

with different indices and signs commuting, fixing `J,q`, and satisfying

```text
[s_i^-,z_j]=q^(delta_ij),
[s_i^+,z_j]=(Jq)^(delta_ij).                                  (BPR1)
```

These relations define a finite class-two 2-group `R` in which `D` is the
shared abelian subgroup. On the `q=-1` spectral subspace of an `R`-module, the
pairs `(z_i,s_i^-)` are Pauli; on the `q=+1` spectral subspace, the pairs
`(z_i,s_i^+)` are Pauli. Consequently the `z`-characters are balanced inside
each raw `q` spectral branch of `R`.

The reset is uniform and finite because `k` is fixed, and it may be attached
to a marked base by amalgamation. This statement does **not** identify raw
`q` with the center of a Schur child. In fact
`raw-schur-generator-is-not-child-center` shows that using `q=q_(N+1)` in the
Schur packet balances the wrong decomposition. A child-multiplicity reset
still requires groupification of the corrected coefficient `Q_f`.
