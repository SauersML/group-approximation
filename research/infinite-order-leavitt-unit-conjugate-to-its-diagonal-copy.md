---
rg: 2
id: infinite-order-leavitt-unit-conjugate-to-its-diagonal-copy
kind: claim
title: Some unit of infinite order of the binary Leavitt algebra over F_2 is conjugate to its diagonal copy, equivalently L ⊗ F_2[t^±1] embeds unitally in L
distinct_from:
  leavitt-units-are-not-conjugate-to-diagonal-copies: that is the negation of this claim; this is the positive statement, recorded so that routes can consume it.
  leavitt-endomorphism-relative-commutants-are-finite: that asks every relative commutant C_u to be finite-dimensional; this asks one C_u to contain a unit of infinite order, which that claim forbids.
  no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2: a unital map L ⊗ L -> L would give this claim, with y the image of 1 ⊗ c; this asks only for a central Laurent variable, not a second copy of L.
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `φ(z) = s_0 z t_0 + s_1 z t_1`. There are units `u, y` of `R` with `y` of
infinite order and `y = u φ(y) u^(-1)`.

**Equivalent forms.**
- (a) Some relative commutant `C_u = C_R(ρ_u(R)) = {z : z = u φ(z) u^(-1)}` contains a unit of infinite order.
  This is the formula in `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`, Attempts, step 3.
- (b) There is a unital embedding `L_(F_2)(1,2) ⊗ F_2[t^±1] -> L_(F_2)(1,2)`.
  - Given `u, y`, the map `r ⊗ t^k -> ρ_u(r) y^k` is a unital homomorphism. Its kernel is `L ⊗ I` for an ideal
    `I` of `F_2[t^±1]`, because `L` is central simple. `I = 0` because `y` is transcendental
    (`unit-roots-divide-centralizer-rank`, part 3).
  - Conversely, an embedding restricts on `L ⊗ 1` to some `ρ_u` (op. cit., step 1), and the image `y` of
    `1 ⊗ t` lies in `C_u` and has infinite order.

**Consequence.** It gives `T̄ <= U` and `(Q,+) <= U` (`rationals-in-leavitt-units-via-diagonal-copy`).

## Attempts

- **Constant matrices are conjugate to their diagonal copies, but are torsion.** Take `a in GL_m(F_2)` and view
  `a ⊗ 1` in `M_m(R) ≅ R`. Its `k`-fold diagonal copy is `a ⊗ 1_(M_k(R))` in `M_m(M_k(R))`. Under the unital
  isomorphism `M_k(R) ≅ R` of a prefix code this is again `a ⊗ 1`, up to conjugation by a Thompson unit. So
  `a ⊗ 1` is conjugate to its diagonal copies. This is the mechanism of `integral-leavitt-unit-group-contains-q`, whose transvection
  `1 + x_(01) y_(00)` is such an element. In characteristic 2 every such element has finite order, and the
  transvection has order 2. So that construction gives nothing modulo 2. The same holds for any unipotent: in
  characteristic 2, `1 + n` with `n` nilpotent has 2-power order.
- **Traces.** A solution needs `Tr(y^j) = 0` for all `j` (`leavitt-units-are-not-conjugate-to-diagonal-copies`,
  Attempts), and the whole span of the resulting `Z[1/2]` lies in `[R,R]` (`leavitt-germ-traces-satisfy-frobenius`).
- **Where it stands.** No infinite-order element of any `C_u` is known. Core and triangular `u` give
  finite-dimensional `C_u` (`leavitt-triangular-endomorphism-commutants-are-finite`), so a solution needs a `u`
  with components of both signs.
