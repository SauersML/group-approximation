---
rg: 2
id: hyperbolic-rf-question-reduces-to-one-fixed-host-proof
kind: route
title: Take a common Olshanskii quotient of the fixed host and a finite-quotient-free group
target: hyperbolic-rf-question-reduces-to-one-fixed-host
requires:
  - kapovich-wise-rf-iff-finite-quotients
  - olshanskii-g-subgroup-quotient-theorem
---

**(3) => (1).**  An infinite group without nontrivial finite quotients is not
residually finite.  **(2) => (3)** is the case `M = empty`.

**(1) => (2).**  By Kapovich--Wise some infinite hyperbolic `G_0` has no
nontrivial finite quotient.  It is non-elementary (infinite elementary groups
are residually finite).  Put `G_1 = G_0/E(G_0)`: hyperbolic, non-elementary,
finite-quotient-free, trivial finite radical.  Let `L = G_1 * H`, a
non-elementary hyperbolic group (free products of hyperbolic groups are
hyperbolic, as quoted in `residual-prime-torsion-via-free-factor`).

*Finite radicals.*  Let `X in {G_1, H}` and let `F <= L` be finite and
normalized by `X`.  By Kurosh, `F <= uAu^(-1)` for a factor `A` and some `u`.
Free factors satisfy: `u^(-1)Bu intersect A != 1` for factors `A, B` forces
`B = A` and `u in A`.
- If some `x in X` has `w = u^(-1)xu notin A`, then
  `F <= u(A intersect wAw^(-1))u^(-1) = 1` by malnormality of `A`.
- Otherwise `u^(-1)Xu <= A`, so `X = A` and `u in A`.  Then `F <= A` is normal
  in `A`, hence `F = 1` since `E(A) = 1`.

So `E_L(G_1) = E_L(H) = E(L) = 1`.  The conjugation kernels on `E(L)` are then
the whole groups, both index conditions read `1 = 1`, and by clause 1 of
`olshanskii-g-subgroup-quotient-theorem` both factors are G-subgroups.

*Quotient.*  For finite `M subset H subset L`, clause 2 gives `φ : L -> Q` onto
a non-elementary hyperbolic group, injective on `M`, with
`φ(G_1) = φ(H) = Q`.  Put `π = φ|_H`: a surjection injective on `M`.  Any
finite quotient of `Q` pulls back to a finite quotient of `G_1`, so it is
trivial.  `QED`
