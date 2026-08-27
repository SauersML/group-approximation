---
rg: 2
id: irs-character-cylinder-counterexample-proof
kind: route
title: Compare two explicit conjugation-invariant mixtures of subgroups of S3
target: irs-character-does-not-determine-haar-cylinders
requires: []
---

All four measures appearing in `(ICD2)` are conjugation invariant, so `mu`
and `nu` are IRSs.  The conjugacy classes of elements of `S_3` are the
identity, the three transpositions, and the two three-cycles; it suffices to
compare the character on these classes.

Every sampled subgroup contains the identity.  A fixed transposition `s`
belongs to the `S_3` atom of `mu` and not to its trivial-subgroup atom, so its
`mu`-probability is `1/4`.  Under `eta_2`, exactly one of the three equally
likely order-two subgroups contains `s`, while `A_3` does not.  Hence

```text
Pr_nu[s in H]=(3/4)(1/3)=1/4.
```

A fixed three-cycle `r` again has `mu`-probability `1/4`.  It belongs to no
order-two subgroup and does belong to `A_3`, giving `nu`-probability `1/4`.
This proves `(ICD1)`.

For the joint event, under `mu` both `s` and `r` occur exactly at the `S_3`
atom, of mass `1/4`.  Under `nu`, an order-two subgroup cannot contain `r`
and `A_3` cannot contain `s`; the event is empty.  This proves `(ICD3)`.

If `q:F_2 -> S_3` is onto, send a random subgroup `H<S_3` to `q^(-1)(H)`.
This equivariant map sends IRSs to IRSs.  Membership of `g in F_2` is
membership of `q(g)` in `H`, so equality of characters and the differing
joint cylinder for chosen lifts of `s,r` both persist.
