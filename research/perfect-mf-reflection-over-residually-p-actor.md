---
rg: 2
id: perfect-mf-reflection-over-residually-p-actor
kind: claim
title: A perfect MF-invisible kernel over a residually-p actor is every classical residual at once
root: true
artifacts:
  - research/perfect-reflection-lower-central-calculus-proof.md
---

Let

```text
1 -> B -> K -pi->> T -> 1                              (PRP1)
```

be a split extension of countable groups.  Assume `B` is perfect and
precomposition with `pi` induces

```text
Hom(T,M)~=Hom(K,M)                                     (PRP2)
```

for every MF group `M`.  If `T` is residually a finite `p`-group for some
prime `p`, then

```text
B=Rad_MF(K)
 =finiteResidual(K)
 =finitePResidual(K)
 =nilpotentResidual(K)
 =solvableResidual(K)                                  (PRP3)
```

and, algebraically,

```text
B=intersection_(j>=1) lowerCentral_j(K)
 =intersection_(j>=0) derived_j(K).                    (PRP4)
```

More precisely, for every `j`,

```text
lowerCentral_j(K)=pi^(-1)(lowerCentral_j(T)),
derived_j(K)=pi^(-1)(derived_j(T)).                    (PRP5)
```

The quotient map also induces canonical isomorphisms on the profinite,
pro-`p`, pronilpotent, prosolvable, and Bohr completions.  Thus the same
perfect subgroup can be simultaneously invisible to every finite,
nilpotent, solvable, compact, and MF target while being recovered
intrinsically as either standard descending-series core.
