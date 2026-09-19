---
rg: 2
id: extraspecial-spin-centralization-phase-death-proof
kind: route
title: Read phase death from the extraspecial commutator pairing
target: extraspecial-spin-predicate-centralization-kills-phase
requires: []
---

Let `E` be extraspecial with `Z(E)=<J>` of order two.  The commutator form
on `E/<J>` is nondegenerate, so for every noncentral `p in E` there is
`x in E` with `[p,x]=J`.

Suppose a toric clause has player component `p`; write it as `beta p b`,
where `b` lies in the other commuting player group.  Normal closure of the
clause centralizes its player component, and therefore

```text
1=[beta p b,x]=[p,x]=J.
```

Thus imposing such a clause kills the desired common phase.  A private
conjugator does not change the conclusion: for `a=t^(-1)pt` and
`y=t^(-1)xt`, one has `[a,y]=t^(-1)[p,x]t=J` whenever `t` fixes `J`.
Consequently neither a noncentral extraspecial spin word nor one private
conjugate of it can be centralized by a phase-safe toric clause retaining
`J`.
