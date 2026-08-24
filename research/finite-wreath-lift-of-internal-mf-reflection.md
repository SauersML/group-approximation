---
rg: 2
id: finite-wreath-lift-of-internal-mf-reflection
kind: claim
title: Finite block wreathing lifts any internal MF reflection back into the Leavitt unit group
root: true
artifacts:
  - research/finite-wreath-lift-of-internal-mf-reflection-proof.md
---

Let `U=L_(F_2)(1,2)^x`, let `K<=U`, and let `pi:K->>Q` satisfy

```text
Hom(Q,M)~=Hom(K,M)                                      (FWL1)
```

naturally by precomposition for every MF group `M`.  For every finite group
`F`, there is an internal embedding

```text
K wr F=K^F semidirectProduct F<=U.                      (FWL2)
```

The coordinatewise quotient induces

```text
Pi:K wr F->>Q wr F,
ker(Pi)=ker(pi)^F,                                      (FWL3)
```

and precomposition with `Pi` is again a natural bijection

```text
Hom(Q wr F,M)~=Hom(K wr F,M)                            (FWL4)
```

for every MF group `M`.  Consequently

```text
Rad_MF(K wr F)=Pi^(-1)(Rad_MF(Q wr F)),                 (FWL5)

cl_MF^(K wr F)(N)
 =Pi^(-1)(cl_MF^(Q wr F)(Pi(N)))                        (FWL6)
```

for every normal subgroup `N` of `K wr F`.  In particular, if `Q wr F` is
MF, then

```text
Rad_MF(K wr F)=ker(pi)^F.                               (FWL7)
```

If `ker(pi)` is normally generated in `K` by one element `d`, then the copy
of `d` in one coordinate normally generates the radical in `(FWL7)`.

The theorem applies unchanged to any target class for which `(FWL1)` holds.
Thus finite, compact, profinite, unitary finite-dimensional, and all-field
linear reflection data can be lifted through the same internal finite wreath
layer.
