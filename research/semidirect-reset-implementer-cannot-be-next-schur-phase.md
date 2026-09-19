---
rg: 2
id: semidirect-reset-implementer-cannot-be-next-schur-phase
kind: claim
title: A bare semidirect reset implementer cannot be the next Schur commutator phase
distinct_from:
  flip-endpoints-cancel-schur-current: that shows a small flip endpoint fuses the two child types; this is an abelianization obstruction to using the flip itself as a coefficient in any reverse Schur packet.
  weyl-derivative-reset-preserves-schur-spin-scale: that constructs the forward fixed-scale reset packet; this proves why the same finite semidirect product does not automatically provide the reverse packet.
---

Let `R=H semidirect <s>` be a split semidirect product with `s^2=1`, and let

```text
chi:R -> C_2,          chi(H)=0,       chi(s)=1.         (SRI1)
```

Then no commutator in `R` equals `s h` for `h in H`. In particular, no
subgroup of `R` can be a Schur packet having `s` with odd exponent in one of
its defining commutator phases.

Indeed every commutator maps to zero under every homomorphism to an abelian
group, while `chi(sh)=1`. Applied to the Weyl derivative reset, this means
the fresh commuting involution `s_i` is a valid selector chart coordinate but
cannot drive the affine commutator matrix of the next baseline inside the bare
reset group. A reverse cell must enlarge the group so that the diagonal copy
of `s_i` enters the derived subgroup, while retaining an equal-scale spin
overlap.

