---
rg: 2
id: nonsofic-hyperbolic-question-reduces-to-one-fixed-host-proof
kind: route
title: Transfer tables through local embeddings and take a common Olshanskii quotient of the host, a bad group and a finite-quotient-free group
target: nonsofic-hyperbolic-question-reduces-to-one-fixed-host
requires:
  - local-approximation-properties-are-marked-closed
  - olshanskii-g-subgroup-quotient-theorem
  - kapovich-wise-rf-iff-finite-quotients
  - residually-finite-groups-are-lef
---

Soficity and hyperlinearity are instances of `P_M`
(`local-approximation-properties-are-marked-closed`), and finite groups have
both. So we work with a general `P_M` that holds for finite groups.

**Finite groups having `P` implies LEF groups having `P`.** Let `G` be LEF,
let `F subset G` be finite and let `eps > 0`. Choose an injective partial
homomorphism `psi` from `F_1 = F ∪ F.F ∪ {1}` into a finite group `Phi`. Then
`psi` is a bijection from `F ∪ F.F` onto `psi(F) ∪ psi(F).psi(F)`. It respects
the products of pairs from `F` and fixes `1`. So `tab_G(F) ≅ tab_Phi(psi(F))`,
and `M(tab_G(F), eps)` holds because `Phi` has `P`. With
`residually-finite-groups-are-lef`, every residually finite group has `P`.

**(1) => (2).** A hyperbolic group is LEH, with `psi` the inclusion.

**(2) => (1).** Let `K` be LEH and failing `P`. Some finite `F` and `eps`
have `M(tab_K(F), eps)` false. The same argument as above, with a hyperbolic
target `H` in place of `Phi`, gives `tab_K(F) ≅ tab_H(psi(F))`. So `H` fails
`P`.

**(3) => (4)** is the case `M = empty`. **(4) => (1)** is immediate.

**(1) => (3).** Let `G = <x_1, ..., x_k>` be hyperbolic and failing `P`. By
clause 3 of `local-approximation-properties-are-marked-closed` there is a
radius `R` with the following property: every marked group whose words of
length `<= R` satisfy the same equalities as in `G` fails `P`.

*A finite-quotient-free partner.* `G` is not residually finite, because
residually finite groups have `P`. By `kapovich-wise-rf-iff-finite-quotients`
some infinite hyperbolic `G_0` has no nontrivial finite quotient. `G_0` is
non-elementary, since infinite elementary groups are virtually cyclic and hence
residually finite. Put `G_1 = G_0 / E(G_0)`. It is hyperbolic,
non-elementary, finite-quotient-free, and `E(G_1) = 1`.

*The amalgam.* Let `L = G * T * G_1`. It is a non-elementary hyperbolic group
(free products of hyperbolic groups are hyperbolic, as in
`hyperbolic-rf-question-reduces-to-one-fixed-host-proof`).

*Finite radicals.* Let `X` be `T` or `G_1`, a free factor with `E(X) = 1`,
and let `F <= L` be finite and normalized by `X`. By Kurosh,
`F <= u A u^-1` for some factor `A` and some `u in L`.
- If some `x in X` has `w = u^-1 x u notin A`, then
  `u^-1 F u <= A cap w A w^-1 = 1`, by malnormality of free factors.
- Otherwise `u^-1 X u <= A`. Since distinct conjugates of free factors meet
  trivially and `X != 1`, this forces `X = A` and `u in A`. Then `F <= A` is
  normal in `A`, so `F <= E(A) = 1`.

Hence `E_L(T) = E_L(G_1) = 1`. Also `E(L) = 1`, because `E(L)` is normalized
by `T`. Both conjugation kernels are the whole groups and both indices equal
`1`. By clause 1 of `olshanskii-g-subgroup-quotient-theorem`, `T` and `G_1`
are G-subgroups of `L`.

*The quotient.* Let `M subset T` be finite, and put
`M' = M ∪ B_R(G) ∪ {1}`, where `B_R(G)` is the ball in the generators `x_i`.
Clause 2 of `olshanskii-g-subgroup-quotient-theorem` gives an epimorphism
`phi : L -> Q` onto a non-elementary hyperbolic group. It is injective on `M'`
and satisfies `phi(T) = phi(G_1) = Q`. Put `pi = phi|_T`. It is surjective and
injective on `M`.

- *`Q` fails `P`.* Mark `phi(G)` by the elements `phi(x_i)`. Take a word `w`
  of length `<= R`. If `w = 1` in `G` then `phi(w) = 1`. If `w != 1` in `G`,
  then `w` and `1` are distinct points of `B_R(G) subset M'`, so
  `phi(w) != phi(1) = 1`. So `phi(G)` agrees with `G` on words of length
  `<= R`, and it fails `P`. Since `P` is hereditary, `Q ≥ phi(G)` fails `P`.
- *No finite quotients.* A finite quotient of `Q` pulls back along the
  surjection `phi|_{G_1}` to a finite quotient of `G_1`, so it is trivial.

`QED`

**Kazhdan host.** A torsion-free infinite group has trivial finite radical,
so (3) applies to `T`. A quotient of a Kazhdan group is Kazhdan. The
marked-limit statement is (3) applied to `M = B_n(T)` for each `n`.

**Note on torsion.** Unlike the residual-finiteness reduction, `Q` is not
claimed torsion-free, because `G` may have torsion.
