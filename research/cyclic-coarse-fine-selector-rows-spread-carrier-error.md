---
rg: 2
id: cyclic-coarse-fine-selector-rows-spread-carrier-error
kind: claim
title: A cycle of coarse-to-fine selector rows charges the total mass of arbitrarily mismatched carriers
distinct_from:
  coarse-fine-selector-covariance-has-quarter-trace-floor: that compares a coarse and a fine selector under one common carrier identity; this permits a different carrier and arbitrary mass at every vertex, with the cyclic sum eliminating all reservoir mismatch
  even-partial-swap-star-has-canonical-trace-floor: that needs orthogonal ranges from one common source and reads a product-word trace; this uses no range orthogonality or swap-star product, only individual mixed selector rows around a cycle
  trace-cyclic-rank-mismatch-checksum: that compares the traces of two approximate products for one pair of projections; this sums projection-conjugacy defects around a cycle of independently sized packet carriers
  atlas-supercritical-pauli-branching-cycle: that asks for a decoded supercritical branch network with leakage and cross-Gram control; this is an unconditional finite-matrix inequality once one coarse and one fine selector have been decoded at each vertex
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial matrix algebra.  For
indices in `Z/kZ`, let `P_i` be arbitrary projections, and let

```text
e_i,f_i<=P_i,       tau(e_i)=tau(P_i)/2,
                    tau(f_i)=tau(P_i)/4.               (CCS1)
```

No equality, orthogonality, or common ambient packet identity is required
among the `P_i`.  For arbitrary unitaries `U_i in M`, put

```text
delta_i=||U_i e_i U_i^*-f_(i+1)||_2.                   (CCS2)
```

Then

```text
sum_i delta_i^2 >= (1/4) sum_i tau(P_i).               (CCS3)
```

In particular, if the total decoded carrier mass is at least `beta`, at least
one of the `k` rows pays squared error `beta/(4k)`, and the total row energy
pays `beta/4`.  Every local multiplicity twist is already included: replacing
`U_i` by `(physical prefix swap) tensor V_i` for arbitrary unitaries `V_i`
does not change the statement or its constant.

There is an ordinary reflection-row form.  Set

```text
R_(e_i)=1-2e_i,       R_(f_i)=1-2f_i,
C_i=R_(f_(i+1)) U_i R_(e_i) U_i^*.                    (CCS4)
```

Then exactly

```text
||C_i-1||_2^2=4 delta_i^2,
sum_i tau(P_i)<=sum_i ||C_i-1||_2^2.                  (CCS5)
```

Thus a bounded cyclic family spreads error without choosing one common
reservoir: local multiplicity can move mass between vertices, but going once
around a `2-to-4` refinement cycle leaves a net trace deficit equal to one
quarter of the total carrier mass.

## Exact Leavitt compatibility

The zero-row geometry is compatible with the properly infinite binary
Leavitt model.  In each copy of the depth-one/depth-two prefix cell, use the
coarse atom `e=s_0t_0`, the fine atom `f=s_(00)t_(00)`, and the established
stabilized three-root unit `J_x` for `x=s_(00)t_0`.  It satisfies

```text
J_x ehat J_x^*=fhat                                    (CCS6)
```

for the stabilized coarse and fine selectors.  Use this same nonzero cell at
every vertex of a `k`-cycle and take every transport to be `J_x`; equivalently,
take `P_i=P`, `e_i=ehat`, `f_i=fhat`, and `U_i=J_x` for all `i`.  All `k`
selector rows are then exact.  There is no contradiction because the Leavitt
algebra is properly infinite and carries no finite trace with the ratios
`(CCS1)`.

## Firewall and remaining compiler target

The cycle removes two real finite-dimensional escapes: unequal carrier masses
and independent multiplicity twists in the transport unitaries.  It does
**not** authenticate the selector reflections in `(CCS4)`.  If all `C_i=1`
were imposed as universal group-algebra identities while the `P_i` were fixed
positive regular-trace packet projections, `(CCS5)` would kill every `P_i` in
the left regular representation.  That is the existing regular firewall, not
a nonhyperlinearity proof.

Accordingly the usable target is matrix-only: decode the `P_i,e_i,f_i` from
canonical finite multiplicities and charge the mixed rows `(CCS4)` to ordinary
word energy without making their selector covariance a zero-defect identity
in every tracial representation.  The cyclic lemma proves that no additional
same-reservoir theorem, Perron--Frobenius recurrence, or control of the local
twists is needed after that decoding step.

Literal quasi-regular involutions remove the reflection syntax but not this
decoding step.  By
`hecke-coset-quarter-selector-is-either-untyped-or-rank-preserving`, a chosen
coset action can make such an involution quarter-negative, but the regular
stationary type makes every nontrivial involution half-negative.  Once finite
type data authenticate the quarter rank, every ordinary HNN/Hecke transport
of those data preserves spectral multiplicity and cannot be a coarse-to-fine
edge.  Thus subgroup averages and finite-edge stable letters do not provide
the missing matrix-only authentication.
