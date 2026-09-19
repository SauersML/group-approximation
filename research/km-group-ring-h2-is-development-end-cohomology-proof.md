---
rg: 2
id: km-group-ring-h2-is-development-end-cohomology-proof
kind: route
title: Compactly supported cochains, the universal coefficient theorem, and the sequence of the pair at infinity
target: km-group-ring-h2-is-development-end-cohomology
requires:
  - triangle-colimit-rational-h2-vanishes
---

**Step 1.**  By `(RH2)` of `triangle-colimit-rational-h2-vanishes`
(valid for every `Lambda`-module),

```text
H^2(Lambda;Z Lambda) = ker( H^2_Lambda(X;Z Lambda) -> H^2(X;Z Lambda) ).
```

**Step 2 (`H^2_Lambda(X;Z Lambda)=H^2_c(X;Z)`).**  Step 2(b) of the
cited proof collapses the first spectral sequence to the complex
`(+)_sigma (Z Lambda)^(Lambda_sigma)` over orbit representatives.  The
standard isomorphism `C^p_c(X;Z) -> Hom_Lambda(C_p(X), Z Lambda)`,
`c |-> c^`, `c^(tau) = sum_g c(g^(-1) tau) g`, is well defined because
`c` is finitely supported and stabilizers are finite (so only finitely
many `g` move `tau` into the support), is `Lambda`-equivariant, is a
cochain map, and is bijective with inverse "coefficient of the identity"
(K. Brown, *Cohomology of Groups*, VIII.7.5, whose proof uses only
finite stabilizers and finitely many orbits).  Hence
`H^2_Lambda(X;Z Lambda)=H^2_c(X;Z)`.

**Step 3 (the kernel condition).**  By the universal coefficient theorem
with `H_1(X)=0`, `H^2(X;Z Lambda)=Hom(H_2(X),Z Lambda)`, and the
forgetful edge map sends `[c^]` to `z |-> c^(z)=sum_g c(g^(-1)z) g`.
This vanishes for all 2-cycles `z` iff `c(g^(-1)z)=0` for all `g` and
`z`, iff `c` annihilates the `Lambda`-invariant group `Z_2(X)` of
2-cycles (there are no 3-cells in a development of a triangle; in
general replace `Z_2` by cycles and note a cocycle kills boundaries).
Since `H_1(X)=0`, the annihilator of `Z_2(X)` in `Hom(C_2(X),Z)` is
exactly `delta C^1(X;Z)`: a cochain killing `Z_2` factors through
`C_2/Z_2 = B_1 = Z_1`, and `Z_1` is a direct summand of `C_1` because
`C_1/Z_1 = B_0 <= C_0` is free.  Equivalently the annihilator is the
kernel of `H^2_c(X;Z) -> H^2(X;Z)=Hom(H_2(X),Z)`.  This gives the first
equality of `(GR1)`.

**Step 4 (end cohomology).**  The short exact sequence of cochain
complexes `0 -> C^*_c(X) -> C^*(X) -> C^*(X)/C^*_c(X) -> 0` gives the
exact sequence

```text
H^1(X;Z) -> H^1(C^*/C^*_c) -> H^2_c(X;Z) -> H^2(X;Z),
```

and `H^1(X;Z)=0`.  Hence `H^1(C^*/C^*_c) = ker(H^2_c(X) -> H^2(X))`,
the second equality of `(GR1)`; unwinding the connecting map gives the
two concrete descriptions in the statement.

**Step 5 (retract criterion).**  Given in the statement; it uses only
functoriality of `H^2_c` under proper cellular maps and of `H_2` under
cellular maps.
