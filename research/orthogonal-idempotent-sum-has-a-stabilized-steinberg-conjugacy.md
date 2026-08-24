---
rg: 2
id: orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy
kind: claim
title: An orthogonal idempotent sum is Steinberg-conjugate to its stabilized block sum
distinct_from:
  murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness: That treats a named conditional arrow between arbitrary equivalent idempotents; this constructs the canonical arrow from `q direct_sum d` to `(q+d) direct_sum 0` when `qd=dq=0`.
  hs-finite-adaptive-ring-tree-decoder: That needs additive physical carrier mass in matrix microstates; this proves the exact algebraic Morita conjugacy but not additivity of a representation-theoretic spectral support.
  mixed-steinberg-loops-admit-morita-rectangular-model: That permits different object reservoirs; this identifies the precise stabilized same-object equation which any remaining rectangular escape must still interpret nonadditively.
---

**ESTABLISHED.**  Let `q,d` be orthogonal idempotents in a unital ring:

```text
q^2=q,       d^2=d,       qd=dq=0.
```

In `M_2(R)` put

```text
p=diag(q,d),                 r=diag(q+d,0),
s=[[q,d],[0,0]],             sbar=[[q,0],[d,0]].        (OSC1)
```

Then

```text
sbar s=p,       s sbar=r,
s p=s=r s,      p sbar=sbar=sbar r.                    (OSC2)
```

Thus `murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness` gives a
fixed stabilized elementary word conjugating `p` to `r`.  Under the standard
Morita flattening of matrix coefficients, the root word for `p` is the
two-block root table for `q` and `d`, while the root word for `r` is the
root table for `q+d` with one zero block.

Therefore every abstract unitary representation of the wordized Steinberg
group sees these two **stabilized packets** as exactly conjugate.  The
remaining normalized-HS issue is not algebraic identification of the sum;
it is whether the physical mass assigned to a block root table is the sum of
the masses assigned to its two diagonal coefficient blocks.  Arbitrary
group representations need not have that Morita-trace property.
