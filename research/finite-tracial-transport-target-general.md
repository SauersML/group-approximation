---
rg: 2
id: finite-tracial-transport-target-general
kind: route
title: The central-sign and finite-normal obstructions over faithfully traced coordinates
target: finite-tracial-cstar-transport
requires: [faithfully-traced-unital-coordinates, finite-traced-kazhdan-transport]
artifacts:
  - GroupApproximation/Sofic/KazhdanSignCriterion.lean
  - GroupApproximation/Sofic/FiniteNormalCoronaObstruction.lean
  - GroupApproximation/Sofic/FiniteNormalCompressionObstruction.lean
  - notes/NO_ONE_SIDED_GROWTH.md
  - non_mf_groups_exist.tex
---

## The class

`C_ftr`: unital C-star algebras with a faithful tracial state.  It contains
the matrix coordinates `(M_d, tr_d)`, all finite-dimensional C-star algebras
with a faithful trace, all UHF and AF algebras with a faithful trace, all
finite von Neumann algebras with a faithful normal trace, and is closed under
corners, finite direct sums and matrix amplification.  Write

```text
Q_A = prod_k A_k / directSum_k A_k
```

for the corona of a sequence from `C_ftr`; the matrix corona is the case
`A_k=M_(d_k)`.

## Target-general theorem

Let `H` be a group with Kazhdan-compression data: `Gamma` with property
`(T)`, `iota : Gamma -> H`, an element `t` with
`t iota(Gamma) t^(-1) <= iota(Gamma)`, and `c` centralizing `iota(Gamma)`.
Put `d = t c t^(-1)`.  Then every homomorphism `rho : H -> U(Q_A)`

* kills every central involution which is the square of a pointwise
  compression defect `[d, iota(gamma)]`, and
* kills every finite normal subgroup of `H` contained in the normal closure
  of those defects.

Consequently a group carrying such data with a nontrivial mark embeds in the
unitary group of *no* corona of faithfully traced unital C-star algebras, not
merely of no matrix corona.

## Why sufficient

**Unitary lifting.**  A unitary of `Q_A` lifts to `x_k` with
`||x_k^*x_k-1|| -> 0`; polar decomposition gives isometries
`u_k = x_k(x_k^*x_k)^(-1/2)`, which are unitary because each `A_k` is finite
(item 1 of `faithfully-traced-unital-coordinates`).  So `rho` is carried by
an operator-norm asymptotic representation `U_k : H -> U(A_k)`.

**The corner.**  Suppose the central involution `zeta` satisfies
`rho(zeta) != 1`.  Since `zeta^2=1` and `zeta` is central, `rho(zeta)` is a
self-adjoint unitary commuting with `rho(H)`, so

```text
P = (1-rho(zeta))/2 != 0,   rho(h) P rho(h)^* = P.
```

By items 2 and 3 of `faithfully-traced-unital-coordinates`, `P` lifts to
projections `p_k`, nonzero along an infinite index set, and
`P Q_A P` is the corona of `(p_kA_kp_k, tau_k(p_k . p_k)/tau_k(p_k))`, again a
sequence from `C_ftr`.  Compression does not increase operator-norm defects,
so `h |-> P rho(h)` is carried by an operator-norm asymptotic representation
in the corner coordinates, and there `rho(zeta) = -1`.  This is the step that
is available only because operator-norm data survives compression by a
projection of arbitrarily small trace.

**Transport in the corner.**  `c` centralizes `iota(Gamma)`, so in the corner
`[U_k(c), U_k(iota gamma)] -> 0` in operator norm, hence in
`||.||_(2,tau_k)`.  By `finite-traced-kazhdan-transport` --- applicable
because the corner coordinates carry tracial states --- the conjugates
`U_k(t)U_k(c)U_k(t)^*` are again asymptotic commutants; asymptotic
multiplicativity identifies them with `U_k(d)` up to a null sequence.  For
unitaries `||AB-BA||_2 = ||A^(-1)B^(-1)AB-1||_2`, so

```text
||U_k([d,iota gamma])-1||_(2,tau_k) -> 0,
```

and `||u^2-1||_2 <= 2||u-1||_2` gives the same for the square.  But the
square is `zeta`, which in the corner is the scalar `-1`, at normalized
`2`-distance exactly `2` from `1` because `tau_k` restricted to the corner is
a state.  Contradiction; hence `rho(zeta)=1`.

**Finite normal subgroups.**  Let `F <= H` be finite normal and contained in
the normal closure of the defects `[d, iota(gamma)]`, and suppose
`rho|_F != 1`.  Because `rho|_F` is a genuine unitary representation of a
finite group inside `Q_A`, the averaged projection

```text
P_triv = (1/|F|) sum_(f in F) rho(f),   P = 1-P_triv
```

is an honest projection, and `P` is `rho(H)`-invariant because `F` is normal.
`P != 0`: otherwise `P_triv=1`, and `1` is an extreme point of the unit ball
of a unital C-star algebra, so a convex combination of unitaries equal to `1`
forces `rho(f)=1` for every `f`.  Compress to `P` as above; the corner lies in `C_ftr` and its
trace is a state `tau`.  Since `rho|_F` has no trivial isotypic component
there,

```text
(1/|F|) sum_(f in F) tau(rho(f)) = tau(P_triv P)/tau(P) = 0.   (N1)
```

On the other hand each `f in F` is a *fixed* word in finitely many
conjugates of the defect generators; conjugation preserves `||.||_2` and
`||xy-1||_2 <= ||x-1||_2+||y-1||_2`, so the transport conclusion
`||U_k([d,iota gamma])-1||_(2,tau_k) -> 0` propagates to
`||U_k(f)-1||_(2,tau_k) -> 0` for every one of the finitely many `f in F`,
whence `tau(rho(f))=1` for all `f` and the left side of `(N1)` is `1`.
Contradiction, so `rho|_F=1`.  This is the general-coordinate form of
`finite-normal-compression-obstruction`; finiteness of `F` is what bounds the
word length, and the corner is what makes `(N1)` available.

## What was matrix-bound before

The three companion pieces generalized here are, in the manuscript, the
central-corner reduction (the spectral cut identifying `q_n M_(d_n) q_n` with
`M_(r_n)`), the central-sign criterion, and the finite-normal cancellation;
in Lean they are `KazhdanSignCriterion`, `FiniteNormalCoronaObstruction` and
`FiniteNormalCompressionObstruction`, all stated over
`Matrix (naturalFiniteModel (d n))`.  Each used matrices only through the
identification of a corner with a smaller matrix algebra, which items 2 and 3
of `faithfully-traced-unital-coordinates` supply in general.

## Boundary

Every use of `C_ftr` beyond "has a tracial state" is a corner: faithfulness
of `tau` is needed exactly so that a nonzero corner carries a state, and
finiteness exactly so that corona unitaries lift to unitaries.  The class
therefore cannot be widened to coordinates without faithful traces, and in
particular not to tracial ultraproducts; see
`tracial-coordinate-transport-barrier`.
