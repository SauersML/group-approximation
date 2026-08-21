---
rg: 2
id: cdi-noncartan-bridge-has-two-exact-gates
kind: claim
title: The CDI character reaches a finite central group sector exactly through two projective-basis gates
distinct_from:
  projective-basis-character-criterion: that is the general character criterion; this applies it to the explicit CDI residue, adds the finite-phase gate, and audits finite-index and operator-valued-cocycle alternatives.
  cdi-character-cannot-be-promoted-by-regular-corners: that rules out regular restrictions and finite-support corners; this identifies the only remaining native twisted-sector compiler.
  thom-central-corner-criterion: that compiles a finite twisted sector once given; this determines exactly when the CDI character supplies such a sector.
---

Let `chi` be the CDI non-CE character of the residually finite property-`(T)`
lattice `H`, let `pi=pi_chi`, put

```text
N_chi={h in H: pi(h) is scalar},   K=H/N_chi,
Q=pi(H)'',
```

and let `[omega] in H^2(K,T)` be the multiplier obtained from a section.
The native CDI unitaries compile `Q` into a canonical corner of a **finite**
central extension if and only if both gates hold:

```text
(G1) chi(h)=0 for every h notin N_chi;
(G2) [omega] is torsion.                                (CDI-NC1)
```

If `(G1)` holds, `Q=L_omega(K)`.  If also `(G2)` holds, rephase `omega` to
take values in some finite group `mu_m`, form the corresponding central
extension `K_tilde`, and obtain

```text
Q isomorphic_to q L(K_tilde) q                         (CDI-NC2)
```

for the central character projection `q`.  Since `Q` is non-CE,
`K_tilde` is a non-hyperlinear group.  Thus `(G1)+(G2)` is an actual complete
compiler from the CDI residue to the main goal.

The failure modes are exact.

- Failure of `(G1)` means some coefficient satisfies
  `0<|chi(h)|<1`; the native group unitaries are not an orthogonal
  projective basis, so no central extension built from this scalar kernel has
  `Q` as its regular twisted sector.
- If `(G1)` holds but `(G2)` fails, `Q` is a non-CE twisted group factor with
  an infinite-phase multiplier.  The associated countable central extension
  has no positive-trace central character projection selecting `chi`; finite
  central-sector compilation requires a new torsion reduction.

Finite-index/Q-system operations do not bypass these gates:
`finite-index-extensions-preserve-connes-embeddability` shows that they carry
non-CE upward but do not provide a group-factor identification.  Likewise
the CDI normal form

```text
Q=M_tilde^C rtimes_(beta,w) C
```

has an operator-valued cocycle and a nonabelian base.  Exterior-equivalence
of `w` to a scalar cocycle would still leave the base `M_tilde^C`; one must
additionally give that base a compatible projective group basis.  Since it
contains the original non-CE algebra, that extra step is itself a
canonical-trace bridge, not a formal cocycle untwisting.

