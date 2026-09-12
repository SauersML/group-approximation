---
rg: 2
id: mf-recognition-for-subgroups-of-one-fp-group-is-pi2-complete
kind: claim
title: MF recognition for two-generated subgroups of one fixed finitely presented group is Pi-zero-two complete
distinct_from:
  mf-recognition-two-generator-recursive-is-pi2-complete: that varies the recursive presentation; this fixes one finitely presented ambient group and varies only a pair of words in it.
  mf-recognition-finite-presentations-is-pi2-complete: that asks whether the presented group itself is MF; this asks about a finitely generated subgroup of a fixed group, and is settled.
  fixed-non-mf-mark-query-is-second-level-complete: that classifies a fixed existential template over varying finite presentations; this fixes the ambient group and classifies MF of its subgroups.
---

ESTABLISHED.  There is a finitely presented group `V` (Higman's universal
finitely presented group will do) such that, for pairs of words `(u_1,u_2)`
in the generators of `V`,

```text
{ (u_1,u_2) : <u_1,u_2> <= V is MF }    is Pi^0_2-complete,
{ (u_1,u_2) : <u_1,u_2> <= V is LEF }   is Pi^0_2-complete,           (SV1)
```

and for every subgroup-hereditary property `P` with `residually finite => P
=> MF` (residual finiteness, residual amenability, MAP, MF full group C-star
algebra, ...), `{ (u_1,u_2) : <u_1,u_2> has P }` is `Pi^0_2`-hard.

So no finitely presented group containing the groups `B2(P_e)` admits a
procedure below the second level that sorts its two-generated subgroups into
MF and non-MF, however much is known about `V` itself.

## Proof

*Upper bounds.*  The subgroup `H = <u_1,u_2>` has the recursive presentation
`< u_1,u_2 | all words trivial in V >`, computable from `(u_1,u_2)` because
the word problem of a finite presentation is r.e.  The `Pi^0_2` normal forms
for MF and LEF of recursive presentations apply to it.

*Hardness.*  Let `P_e = B2(S_e)` be the two-generator recursive presentations
of [[mf-recognition-two-generator-recursive-is-pi2-complete]],
on generators `a_e, t_e`.  The free product

```text
Q = *_(e in N) P_e
```

is recursively presented, uniformly.  By Higman's embedding theorem, in the
explicit form of [[mikaelian-explicit-higman-embedding]], `Q` embeds in a
finitely presented group `V` with computable images `u_1(e), u_2(e)` of
`a_e, t_e`.  The free factor `P_e` is the subgroup `<u_1(e), u_2(e)>` of
`V`.  By `(TG2)` it is residually finite for `e in INF` and contains `E` for
`e in FIN`.  Hence `e -> (u_1(e),u_2(e))` is a many-one reduction of `INF`
to each set in `(SV1)` and to the `P`-set for each hereditary `P` between
residual finiteness and MF.

Any finitely presented group containing `Q`, in particular Higman's
universal finitely presented group, may serve as `V`.
