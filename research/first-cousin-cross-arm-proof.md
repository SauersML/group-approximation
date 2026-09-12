---
rg: 2
id: first-cousin-cross-arm-proof
kind: route
title: Separate colliding cousins by fresh Pauli factors and apply the equal-level area fence
target: first-cousin-cross-arm-breaks-three-state-reuse
requires:
  - full-prefix-range-cells-have-three-state-model
  - leavitt-prefixes-form-exponential-heisenberg-packet
  - opnorm-pauli-cross-check-packing-capacity
  - level-synchronous-first-mismatch-area-is-centralizer-impossible
---

In the three-state model, the address products for `00` and `11` are both
the identity permutation.  The corresponding same-role arms therefore have
the same values `X,Z`, with `[X,Z]=J`.  The actual prefix coefficients obey

```text
t_(00)s_(11)=0,
```

so the composable-root commutator between these two occurrences must be one.
This proves that `(CCA1)` rejects the periodic assignment.

For the finite repair, let `m` be the number of retained leaf addresses and
work on

```text
H_m=C^3 tensor (C^2)^(tensor m).
```

Keep the three character signs and all local Whiteheads on the first factor.
Let `P=(1-J)/2`.  For each leaf `alpha`, put

```text
X_alpha=Pauli X on factor alpha,
Z_alpha=(1-P)+P(Pauli Z on factor alpha).              (1)
```

Then

```text
[X_alpha,Z_alpha]=J,
[X_alpha,Z_beta]=1                    (alpha!=beta).   (2)
```

Character permutations commute with every global `X_alpha`.  Their
conjugates of `Z_alpha` are controlled by the appropriate child-character
projection, so the local one-arm Whitehead and range-sum cells extend exactly
as before.  For the first two colliding cousins, `m=2` already repairs the
new row; for the complete depth-two leaf table, `m=4` gives dimension
`3*2^4=48`.  The initial marked projection remains nonzero.

For a depth-`n` complete prefix table, equations `(2)` give
`N=2^n` same-site marked commutators and all off-diagonal cross checks.
`opnorm-pauli-cross-check-packing-capacity` then yields a dimension lower
bound tending to infinity with `N`, even for sufficiently small uniform
operator-norm errors.  This is exactly the capacity input one would feed to
`opnorm-coordinatewise-capacity-diagonal`.

It cannot have the required uniform syntactic input.  If every canonical
equal-level cross discrepancy were a literal conjugate of one of finitely
many null prototypes with fixed fillings, their relator areas would be
bounded by one constant independent of `n` and of the two tails.
`level-synchronous-first-mismatch-area-is-centralizer-impossible` proves that
no such bound exists.  Thus the capacity family cannot arise from this
canonical cross-arm menu with lossless fixed-prototype control.
