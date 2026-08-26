---
rg: 2
id: signed-hecke-literal-pauli-probe-audit
kind: route
title: Enumerate literal middle-Pauli probe extractions on the root-free signed-Hecke classes
target: middle-pauli-probes-leave-three-signed-hecke-detector-classes-untyped
requires:
  - signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped
  - paid-t00-reynolds-cut-is-whitehead-reducing
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
---

Use the faithful binary-prefix normal form in which `(mu,nu)` denotes
`s_mu t_nu`; equality expands shorter right prefixes by

```text
s_mu t_nu
 =s_(mu0)t_(nu0)+s_(mu1)t_(nu1).                     (1)
```

Build exact `9 by 9` elementary matrices over this algebra on coordinates
`(1,2,3,4,5,6,7,8,9)`.  Embed the certified `8192` constant matrices of
`L_0` on `(2,4,5,6,7,8,9)`.  Reuse the existing exact conjugacy/normal
closure audit to select precisely the `31` positive classes whose internal
normal closure contains no root.

Insert the literal factors

```text
a_m=s_1t_(0^m),              b_m=s_(0^m)t_1,
X_m=x_(1,k_m)(a_m),          Y_m=x_(k_m,3)(b_m),      (2)

c_m=s_(0^(m+1))t_(0^m),     d_m=s_(0^m)t_(0^(m+1)),
J_m=x_(k_(m+1),k_m)(c_m)
    x_(k_m,k_(m+1))(d_m)
    x_(k_(m+1),k_m)(c_m).                            (3)
```

Exact multiplication first verifies `J_m^2=1` and
`J_1J_2J_1=J_2J_1J_2`.  Enumerating the eight translation subsets and the
six Coxeter words gives `48` distinct dual matrices and `48` distinct
primal matrices.

For source preservation, conjugate each of the ten signed generators of
`L_0` by every dual word, require that every image be constant, require
membership in the certified `L_0` table, and compare its carried character
bit.  Exactly `1` and `Y_1` pass.  Direct multiplication shows `Y_1`
commutes with all ten generators, so neither permitted source-preserving
probe detects any positive class.

For extraction, allow an arbitrary representative in each `L_0` conjugacy
class; this costs only source-preserving conjugation.  For every dual word
`u`, form the exact matrix commutator `[g,u]`.  Recognize an elementary root
only when the result has identity diagonal and exactly one nonzero
off-diagonal Leavitt coefficient.  Repeat after a second dual word, after
each single `X_m`, and after every word in the primal `48`-menu.  The exact
counts are

```text
elementary [g,u]:                         16/31,
elementary [[g,u],v],      u,v in M_Y:    16/31,
elementary [[g,u],X_m]:                   28/31,
elementary [[g,u],v],      v in M_X:      28/31.       (4)
```

The three failures in the last two rows are `(MPF4)`.  Reading their matrix
entries gives `(MPF5)`, which explains the exhaustive result without a
black-box search: their middle-index interactions eject only to targets
`2,4`, and no primal word changes the source set `{7,8,9}` of its elementary
return legs.  Appending `S_57` and `A_1` as additional single second probes
leaves all three failures because those roots are still not sourced at
`2` or `4`.

The coefficient-free `F_2` skeleton in
`experiments/signed_hecke_middle_pauli_probe_audit.py` independently gives
the same `15` and `3` obstruction lists.  It is only a diagnostic; all
asserted literal counts use the faithful coefficient calculation.  MSI jobs
`17035848` and `17036755` used one CPU each, with the latter adding the
`S_57,A_1` comparison.
