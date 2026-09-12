---
rg: 2
id: z3-level-preserving-automorphisms-uniform-proof
kind: route
title: Specialize to the generic level and apply plane rigidity over F_2(s)
target: z3-level-preserving-automorphisms-rotate-uniformly
requires:
  - order-three-equivariant-plane-automorphisms-are-linear
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Artifact, Section 3, Theorem 4.
1. **Setup.** Write `T(s,v) = (s + b, Phi(s,v))` and `T^-1(s,v) = (s - b, Psi(s,v))`. The two
   inverse identities give `Phi(s - b, Psi(s,v)) = v` and `Psi(s + b, Phi(s,v)) = v`.
2. **Generic level.** Over `K = F_2(s)`, `v -> Phi(s,v)` is an `R`-equivariant polynomial
   automorphism of `A^2_K`. `x^2 + x + 1` stays irreducible there, because `F_2` is algebraically
   closed in `F_2(s)`. By `order-three-equivariant-plane-automorphisms-are-linear`,
   `Phi = lambda(s) v` with `lambda(s)` in `K[R]`.
3. **Constant rotation.** `Phi` has coefficients in `F_2[s]`, so `lambda(s)` lies in `F_2[s][R]`. The
   inverse is polynomial as well, so `lambda(s)` is a unit of `F_4[s]`, hence constant.
