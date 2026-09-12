---
rg: 2
id: index-two-reynolds-proper-section-proof
kind: route
title: Compress the subgroup-Hecke stable letter and subtract its final support
target: index-two-reynolds-hnn-is-a-proper-corner-section
requires:
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
  - central-sign-assignment-atom-is-index-two-reynolds-surplus
---

Put `p=e_C`, `q=e_H`.  The subgroup-Hecke identity is `qup=up`, so
`v=qup` has `v^*v=p` and `vv^*=upu^*<=q`.  Therefore `q-vv^*` is a
projection.  Traciality gives

```text
tau(q-vv^*)=tau(q)-tau(v^*v)=tau(e_H-e_C).
```

For the central-sign pair, the second prerequisite identifies the last
projection with the assignment atom.  The approximate estimate is the
fixed-table exactification and leakage inequality already included in the
first prerequisite.
