---
rg: 2
id: canonical-regular-packets-leave-an-unbounded-cartan-reservoir
kind: claim
title: Canonical regular packets leave an unbounded Cartan reservoir
distinct_from:
  fixed-extraspecial-packet-is-morita-neutral-for-code-rounding: that preserves a contextual code escape under one fixed spin factor; this computes every regular-trace central sector, treats an ideal paired right action, and proves a rank-one-Cartan selector no-go.
  irreducible-finite-packet-normalizer-words-scalarize: that factors ordinary normalizer words on one irreducible sector; this adds the Plancherel multiplicity forced by canonical trace and an explicit diffuse faithful-trace model.
  collision-and-phase-free-cartan-observables-force-joint-lamp-targets: that proves collision and phase-free Cartan observables are sufficient; this proves no fixed finite packet can manufacture the required rank-one Cartan from canonical moments.
  right-regular-covariance-forces-one-common-router: that removes coordinate-dependent gauges inside a fixed finite router while retaining one common multiplicity unitary; this proves that the remaining common unitary is an unbounded reservoir and cannot be removed by another finite regular packet.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED FINITE-PACKET NO-GO; GLOBAL ROUTE OPEN.**  Let (K) be a
finite group, let (
u) be an irreducible representation of dimension
(s), and let (e_
u) be its central idempotent.  Put
(pi_r=rlambda_K), the direct sum of (r) regular representations.
Then

```text
tau(e_nu)=s^2/|K|,
e_nu H_r = C^s tensor C^(rs),
e_nu pi_r(C[K]) = M_s tensor I_(rs),                    (RPC1)
(e_nu pi_r(C[K]))' = I_s tensor M_(rs).
```

Thus selecting a nontrivial central character really does produce a full
finite matrix algebra, but only on the first tensor factor.  Its multiplicity
is forced by the canonical regular trace and grows linearly with the ambient
matrix dimension.

Even granting the strongest operator-level left/right packet does not remove
the reservoir.  On the (
u)-block, left and right regular algebras jointly
give

```text
M_(s^2) tensor I_r,          commutant = I_(s^2) tensor M_r.   (RPC2)
```

An actual second commuting finite group with canonical trace is not the right
regular algebra on the same copy: it is another left regular factor.  Applying
((RPC1)) to the product group again leaves its Plancherel multiplicity.
Hence neither two commuting packet copies nor an extraspecial central sector
kills arbitrary amplification.

This obstruction is basis-theoretic, not merely a dimension count.  If a
finite observable tuple generates (M_S tensor I_m), its pointwise unitary
stabilizer contains (I_S tensor U(m)).  For (m>1), no
unitary-equivariant rule depending only on that tuple can choose a rank-one
masa.  Indeed, connectedness forces every unitary in the stabilizer to fix
each minimal projection of such a masa; those projections would lie in
(M_S tensor I_m) and therefore have rank divisible by (m).

Normalizer covariance does not improve this conclusion.  Every normalizer
of one selected simple sector has the form

```text
U_g=C_g tensor W_g,                                      (RPC3)
```

where (C_g) is a fixed finite-sector implementer and (W_g) is an
arbitrary multiplicity unitary, up to a reciprocal scalar.  Actor products
only impose the corresponding projective relations on the (W_g)'s.  A
rank-one tensor-product Cartan therefore still requires a multiplicity masa
on which all (W_g)'s have the collision and phase-free bounds.  This is
exactly the missing Cartan extraction problem, not rigidity supplied by the
packet.

The failure occurs with exact relations and canonical trace.  Let (F_r)
be the (r)-point discrete Fourier matrix and represent (K times C_4) by

```text
pi_r(k,t^a)=lambda_K(k) tensor F_r^a.                    (RPC4)
```

This is an exact representation, (F_r^4=I), and its normalized character
converges to the canonical group trace.  Nevertheless, in the fixed
packet-product basis,

```text
Col_D(I tensor F_r)=1/r,
inf_(M monomial) ||I tensor F_r-M||_2^2 >=2-2/sqrt(r).   (RPC5)
```

The same lower bound tends to (2) after arbitrary (o(r|K|)) padding.
All finite-packet relations and covariance are exact.  Thus a finite
nonabelian packet can rigidify its finite tensor factor and can collapse
coordinate-dependent gauges to one common router, but it cannot force the
rank-one Cartan or spatialize that common router.

For the order-(27) qutrit Heisenberg group, a nontrivial central character
has (s=3).  Its regular central corner has trace (1/3) and is
(M_3 tensor I_(3r)); the ideal left/right pair is
(M_9 tensor I_r).  This concrete central-character candidate therefore
has exactly the reservoir described above.

The result does not say that a packet-factor masa is useless: its minimal
projections have rank equal to the reservoir dimension and its actor action
is rigid modulo that reservoir.  It says that upgrading those coarse atoms
to the rank-one Cartan required by
`collision-and-phase-free-cartan-observables-force-joint-lamp-targets`
still needs new, growing actor-dependent information.  The Kun--Thom
hyperlinear-to-sofic route remains OPEN.

DERIVATION
regular-packet-central-sector-multiplicity-proof
