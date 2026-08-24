---
rg: 2
id: leavitt-singular-near-excluded-by-local-lift
kind: route
title: Descend the amenable near-state trace and contradict Leavitt nonsoficity
target: binary-leavitt-has-no-purely-singular-free-near-representation
requires:
  - invariant-free-near-state-is-amenable-regular-cover
  - amenable-trace-descends-through-locally-liftable-quotient
  - binary-leavitt-near-regular-quotient-is-locally-liftable
  - openai-leavitt-unit-nonsofic
---

Suppose a purely singular free near-state witness `(H,phi,pi)` for
`Q=L_(F_2)(1,2)^x` existed. The regular-cover theorem gives

```text
A=C^*(pi(Q)),
tau=phi|_A amenable,
A/I_tau ~= C^*_r(Q)                                    (BLD1)
```

trace-preservingly. The local-lifting hypothesis for this exact quotient and
`amenable-trace-descends-through-locally-liftable-quotient` therefore make
the canonical regular trace on `C^*_r(Q)` amenable.

For a discrete group, amenability of the canonical trace on the reduced group
C-star algebra is equivalent to amenability of the group: an invariant
hypertrace restricts to an invariant mean on the diagonal `ell^infinity(Q)`.
Hence `Q` would be amenable. Every amenable group is sofic, contradicting the
established theorem `openai-leavitt-unit-nonsofic`.

Thus the local-lifting terminal alone excludes every singular free near-state;
no normalized-HS stability, `(TT)/T` exactification, or finite-dimensional
representation theory is used.
