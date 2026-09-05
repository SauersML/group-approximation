---
rg: 2
id: stw99-l-dadarlat-aut-homotopy-theorem
kind: claim
title: Dadarlat's KK description of the homotopy of Aut of a UCT Kirchberg algebra
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

For a unital Kirchberg algebra `D` in the UCT class and a locally
contractible compact metric space `X`, the natural map sending a
point-norm continuous family of automorphisms to its `KK`-class
identifies homotopy classes of maps `X -> Aut(D)` landing in the
identity component with a quotient of `KK(D, C(X) (x) D)`, the kernel
being the image described before Dadarlat's Theorem 3.6.  Specialised
to `X = T` this is the statement consumed by
`stw99-l-pi1-aut-splits-into-two-hom-groups`: the reduced class

```text
Delta_alpha  in  KK(D, SD) = KK^1(D, D)
```

of a based loop `alpha` is a complete invariant of its homotopy class
modulo that kernel, the group law being pointwise composition of loops
(the multiplication of reduced classes vanishes for the circle).
Unbased homotopy classes agree with based ones here, since a free
homotopy `H(z,t)` is rebased as `H(1,t)^{-1} H(z,t)`.

Reference: Dadarlat, *The homotopy groups of the automorphism group of
Kirchberg algebras*, Theorem 6.3, Examples 5.4, Remark 6.4,
https://www.math.purdue.edu/~mdd/Publications/Aut.pdf .  This is the
theorem Schafhauser--Tikuisis--White cite in Problem L in the form
`pi_k(Aut(A)) = KK^1(C_u A, S^k A)`.
