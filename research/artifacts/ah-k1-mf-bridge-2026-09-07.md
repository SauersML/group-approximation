# The AH counterexample and the MF programme, and what of it was new

2026-09-07.  Audit of a seventh forwarded dossier, connecting the STW59
AH construction to the ring theorem of the non-MF paper.

## Most of it is already in the graph, and the graph is ahead

- **§2, the exact component group `Z/2`.**  Already
  `stw59-exact-factorial-unitary-component-groups`, established 2026-09-05,
  which computes the entire group as `Z/(n!)` and states the `n = 2` case as
  `Z/2` for exactly this algebra.  The gauge/section fibration, the
  `pi_1 Gamma(S(E (+) 1)) = H^(2r)(X;Z)` obstruction step and the top-Chern
  image computation are its route `stw59-gauge-section-euler-image-proof`.
- **§4, the factorial family `Z/(d!)`.**  Already
  `stw59-simple-ah-factorial-unitary-torsion`, and superseded twice:
  `stw59-exact-arbitrary-cyclic-unitary-component-groups` realizes the whole
  group `Z/d` for every `d >= 2`, not only orders dividing some `d!`, and
  `stw59-exact-finite-abelian-unitary-component-groups` goes past cyclic.
- **`diag(v,1_A)` null-homotopic in `U(M_2(A))`.**  Already a clause of
  `stw59-simple-ah-non-k1-injective`.

## What was new, and is authored

The bridge to the ring theorem, which is where the dossier's own interest
lies.

1. `simple-ah-witness-is-elementary-in-rank-two`.  The recorded statement is
   that `diag(v,1_A)` is null-homotopic.  The dossier upgrades this to an
   **algebraic** factorization: a generator of `pi_4(SU(2))` is null-homotopic
   in `SU(4)` since `pi_4(U(n))` is stable and zero from `n = 3`, a
   null-homotopic determinant-one matrix over `C(S^4)` is a product of
   elementary matrices by subdividing the homotopy and eliminating, and
   `E_4(C(S^4)) = E_2(M_2(C(S^4)))` by block flattening.  So
   `diag(v,1_A) in E_2(A)` and `[v] = 0` in algebraic `K_1(A)`.
2. `unit-abelianization-to-algebraic-k1-not-injective`.  Polar decomposition
   makes `A^x` homotopy equivalent to `U(A)`, so `pi_0(A^x) = Z/2` is a group
   quotient of `A^x` killing every commutator and detecting `v`, while `v`
   dies in algebraic `K_1`.  This is the sharp contrast with
   `agp-purely-infinite-simple-k1-is-unit-abelianization`: for a purely
   infinite simple ring the unit-group abelianization **is** algebraic `K_1`,
   and the AH example shows that conclusion genuinely uses pure infiniteness.
3. `mf-approximation-does-not-give-k1-injectivity`.  `A` is MF, being an
   inductive limit of homogeneous algebras, so every countable subgroup of
   `U(A)` is an MF group, and yet `U(A)/U_0(A) = Z/2` while `K_1(A) = 0`.
   Matrix models preserve the norm and algebraic data of a finite set without
   preserving whether a unitary is connected to the identity inside `A`.

## Trust boundaries

The `c_3 = +-2` computation underlying `Theta(alpha) = +-2` was not
re-derived here; it is the content of the established
`stw59-gauge-section-euler-image-proof` and is taken from there.

The countable-subring variant sketched at the end of the dossier's §3, formed
by repeatedly adjoining fullness witnesses, is recorded here and not
authored: it is a construction sketch and the two statements above do not
need it.

## Not asserted

No literature priority.  Nothing here is formalized.  Nothing here revises
the STW59 lane, which is another session's authored work and is ahead of the
dossier on every point it shares.
