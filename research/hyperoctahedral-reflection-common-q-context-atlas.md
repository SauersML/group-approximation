---
rg: 2
id: hyperoctahedral-reflection-common-q-context-atlas
kind: claim
title: One thin hyperoctahedral reflection carries every balanced BCS context exactly
distinct_from:
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that uses the entire primitive type corner and does not expose an arbitrarily thin common complement.
  standard-type-thin-common-reflection-sector: that supplies the density calculation but leaves the predicate packets unspecified.
---

**ESTABLISHED.**  Let `B` be a finite BCS with a tracial state.  Take a
rational balanced atlas

```text
n_(c,a)>=0,       sum_(a in R_c)n_(c,a)=D,                 (HRC1)
```

as in `tracial-bcs-has-rational-balanced-hyperoctahedral-atlas`.  For every
integer `t>=1`, put `N=tD+1` and

```text
K_N=(C_2)^N semidirect S_N.                               (HRC2)
```

Let `rho_N` be the tautological irreducible signed-permutation representation
on `C^N`, let `p=z_(rho_N)`, and let `s` be the diagonal sign which is `-1`
on coordinate zero and `+1` on all other coordinates.  Set

```text
e=p(1-s)/2,             q=p(1+s)/2.                        (HRC3)
```

Then, relative to the normalized canonical trace on `p`,

```text
tau_p(e)=1/N,           tau_p(q)=tD/(tD+1).                (HRC4)
```

Moreover every context `c` has commuting diagonal involutions `d_(c,x)` in
`K_N` whose joint spectral PVM on `q` is supported inside `R_c`, with the
allowed atom `a` of rank `t n_(c,a)` (and hence possibly zero).  For every
shared variable incidence `(c,d,x)`
there is a permutation `pi_(c,d,x) in S_(N-1)` fixing coordinate zero and
satisfying

```text
pi_(c,d,x) d_(c,x) pi_(c,d,x)^(-1)=d_(d,x).               (HRC5)
```

Thus one literal common projection `q` simultaneously has arbitrarily high
canonical density, carries every nonlinear local predicate exactly, and has
rank-balanced binary overlap fibers.  The construction does **not** make the
incidence permutations coherent around cycles.  Doing so in the root block
would give a forbidden finite-dimensional BCS model.  The only remaining
operation is therefore block-escaping cross-context holonomy, not predicate
encoding, density, or edgewise rank matching.

DERIVATION
hyperoctahedral-reflection-common-q-context-atlas ✓ via hyperoctahedral-reflection-common-q-context-atlas-proof
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas ✓

CANONICAL MATERIAL TO READ
research/hyperoctahedral-reflection-common-q-context-atlas-proof.md
research/tracial-bcs-has-rational-balanced-hyperoctahedral-atlas.md
