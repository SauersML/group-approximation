# Hosts for SL_3(Z[t]): one excluded family and a map of the rest

Lane `bh-char-zero-transcendental`, swarm 5, 2026-09-12. Root:
`char-zero-linear-groups-satisfy-boone-higman`.

**No host for `SL_3(Z[t])` was found.** This lane produced:
- one obstruction that closes the algebraic-host family in characteristic zero at
  once;
- the (T)-based exclusions;
- the families that remain.

## 1. Algebraic unit-group hosts are excluded

This is the new node `char-zero-algebra-unit-hosts-exclude-unipotents`, with route
`char-zero-algebra-unit-hosts-exclude-unipotents-proof`.
- **Statement.** Let `A` be a `Q`-algebra and `C` a group of central units. Let
  `G <= A^x / C` be finitely generated, and suppose some lift in `G~` is a
  central unit times a non-central unipotent. If the lifts live in a subring `B`
  where no non-zero element is divisible by infinitely many primes, then `G` is
  not simple.
- **Proof.** Reduce modulo `p` for large primes. Then `u^p` is central mod `p`,
  so the kernel is non-trivial, and simplicity forces every generator to be
  central mod `p` for infinitely many `p`. So `G` is abelian, and logarithms of
  unipotents give the contradiction.
- **Why it matters.**
  - The positive-characteristic host embeds `GL_n` of a coordinate ring into the
    units of `L_p ⊗ L_p` by matrices, where elementary matrices are unipotent of
    order `p`.
  - In characteristic zero the same mechanism fails for `SL_3(Z)` already, for
    every host algebra with a free integral form, or with coefficients in a
    finitely generated field.
  - This is strictly more than `char-zero-leavitt-unit-groups-have-congruence-kernels`,
    which treats only the full unit group of `L_A(1,2)` over a domain. The new
    node covers finitely generated subgroups, quotients by central units, and
    `Q`-algebras such as `L_Q(1,2) ⊗ L_Q(1,2)`, provided `L_Z(1,2)` has a `Z`-basis.
  - **Unchecked input.** That `Z`-basis should come from the diamond lemma
    (integer relations with leading coefficient 1), but it is not checked here.
    For `L_Q(1,2)` use the second form of (D) only after checking it.
- **Consistency.** Zaremsky's `GL_n(Q)` host is a group of homeomorphisms, and in
  characteristic `p` unipotents have finite order. Neither is affected.

## 2. Hosts excluded by property (T)

Imported, not verified from source in this lane. The MSI connection was down
when this was written.
- Suslin (1977): `SL_n(Z[t]) = E_n(Z[t])` for `n >= 3`.
- Ershov--Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*,
  Invent. Math. 179 (2010): `EL_n(R)` has (T) for `n >= 3` and every finitely
  generated associative ring `R`.

So `SL_3(Z[t])` has (T), and so (FA). Consequences:
- **a-T-menable hosts.** An a-T-menable group has no infinite (T) subgroup, and
  `F`, `T`, `V` are a-T-menable (Farley 2003). So `SL_3(Z[t])` is not in `V`, and
  a V-type host must fail a-T-menability. Such hosts do exist:
  `V_d(Z^3 x| SL_3(Z[1/m]))` contains `SL_3(Z)`.
- **Graph-of-groups towers.** By `fa-subgroups-of-graph-towers-lie-in-base-pieces`
  the input already sits in a base piece. So HNN and amalgam towers,
  `boone-higman-via-decidable-edge-towers` included, add nothing for this input.
- **Groups acting properly on products of locally finite trees.** A (T) subgroup
  fixes a vertex in each factor, and vertex stabilizers are finite. So lattices in
  products of trees, such as Burger--Mozes groups, contain no copy.

## 3. Affine self-similar hosts

- **Commutative coordinates.** Excluded by
  `affine-self-similar-coordinate-rings-are-one-dimensional`.
- **Semilinear virtual endomorphisms (heuristic).** Consider
  `phi(v, g) = (psi(v), sigma(g))`, where:
  - `sigma` acts entrywise through a ring endomorphism of `Z[t]`;
  - `psi` is `sigma`-semilinear on `I^3` for a finite-index ideal `I`.

  Then `I` is isomorphic to `Z[t]` with scalars acting through `sigma`. That
  module is free of rank `deg sigma(t)`, while `I` has rank one. So `sigma` is an
  automorphism and `I` is principal, which is impossible at finite index.
  - **Gap.** Not every homomorphism from a finite-index subgroup of `SL_3(Z[t])`
    is known here to be standard.
- **Noncommutative coordinates (heuristic).** Write each generator as a digit
  plus a generator times `x`. If the digits are central integers and there are
  finitely many generators, the digit sequence of a coordinate is eventually
  periodic. So the coordinate is rational in `x` and commutes with `x`. Any
  noncommutative escape needs non-central digits.

## 4. What remains

- **Homeomorphism hosts.** A finitely presented full Cantor group containing
  standard `V` and a faithful copy of `SL_3(Z[t])` gives Boone--Higman for
  `SL_3(Z[t])`, by `fp-full-binary-cantor-groups-have-type-a-actions`. The known
  families are Rover--Nekrashevych groups and twisted Brin--Thompson groups, and
  by Section 3 the self-similar input cannot be affine over a commutative ring.
- **A candidate Cantor action.** `SL_3(Z[t^(+-1)])` acts on the compact group
  `Y = (Z_p^3)^Z` of bi-infinite coefficient sequences, by Laurent-polynomial
  matrices.
  - **Faithful.** A matrix `M` sends `e_i` placed at coordinate 0 to column `i`
    of `M`.
  - **Continuous and finite-state in both directions.** An output coordinate is
    a fixed integer combination of boundedly many input coordinates. In the
    `Z`-direction this is a cellular automaton; in the `p`-adic direction it is a
    finite-state transducer with bounded carries.
  - **The two-direction analogue of Zaremsky's rational affine maps.** A full group on
    `Y` built from these maps and the `p`-adic and shift splittings is a
    Brin--Thompson-type group with infinitely many directions.
  - **Open.** Whether some finitely generated full group of this kind that
    contains `SL_3(Z[t])` is finitely presented. This is the natural next target.
- **Unit groups over `Q`-algebras violating (D).** For example a finitely
  generated ring that contains `Q`. Nothing is known here about their unit groups.
