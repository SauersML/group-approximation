---
rg: 2
id: constant-hs-groupification-of-residual-dyadic-splitter
kind: claim
title: Finitely groupify an adaptive dyadic splitter on the residual Schur commutant
distinct_from:
  constant-hs-groupification-of-residual-dimension-tape: that drives the same residual contradiction through additive polynomial identities and formal inverses; this uses only bounded Pauli flip cells and tests residual atomic granularity directly.
  residual-commutant-supercritical-schur-trigger: that states the desired output without selecting its internal computation; this proposes nested full-support cell splitting as the group-native computation.
---

Construct a finite group-word machine which, inside the residual commutant of
`(RMT1)`, recursively bisects one full-support packet cell by the explicit
Schur flip square.  For every finite-dimensional microstate with residual
factor `M_L(C)`, either it pays a universal energy floor or it reaches a depth

```text
r>log_2L                                                        (RDS1)
```

at which all `r` Pauli pairs remain independent on the same positive-density
carrier.  Splitting, synchronization, central-sign retention and return must
cost at most `C E_rel`, where `C` is independent of `L` and `r`.

The exact tracial model must realize the recursion in a nested dyadic matrix
tower inside a diffuse residual factor.  The control rule choosing when to
stop must be microstate-dependent: no externally fixed depth can distinguish
that model from arbitrarily large matrices.

## Attempts

- Sequential word telescoping spends error proportional to depth and yields
  only a large hyperlinear profile.
- Testing the terminal minimal projection directly loses its signal as
  `2^(-r)`; the actuator must retain the common central sign on the entire
  residual carrier, not merely mark one leaf.
- A fixed self-similar split relation has finite cyclic truncations.  Boundary
  wraparound must either occur on positive density through a PCP/expander
  check or trigger the next split from finite-multiplicity data.
- Recursive verifier compression is the live mechanism for depth-independent
  soundness.  The remaining bridge is to make its local checks act as the
  explicit Schur flip automorphisms while preserving perfect diffuse
  completeness.
- `commuting-schur-replicas-force-exponential-dimension` proves that a
  constant forbidden-mass gap across `N` commuting replicas already yields
  dimension at least `2^(beta_B N/C)`, even though different replicas may
  select different violated contexts.  Thus the compiler need not align one
  specific predicate across depth; it only must recover the commuting replica
  structure and choose `N` at the residual matrix scale.
- If the controller emits the *complete multiplication table* of the selected
  finite replica group with one fixed all-pairs error, Gowers--Hatami
  exactifies the whole object with constants independent of `N`.  The robust
  endpoint is `approximate-schur-replicas-force-exponential-dimension`; the
  remaining table compiler is
  `adaptive-all-pairs-schur-replica-table-compiler`.
- For existence of one nonhyperlinear group, internal dimension detection is
  stronger than necessary.  The independent Kleene route lets a bad-witness
  search output its own dimension and asks the halting compiler to defeat only
  that dimension.  This leaves the same runtime-independent table lowering but
  removes residual polynomial identities and microstate-dependent stopping
  from the group gadget itself.
