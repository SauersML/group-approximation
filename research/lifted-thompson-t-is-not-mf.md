---
rg: 2
id: lifted-thompson-t-is-not-mf
kind: claim
title: "Every homomorphism from the lifted Thompson group T-bar to the unitary group of a norm matrix corona kills the central translation z"
distinct_from:
  lifted-thompson-t-mf-radical-dichotomy: that is the unconditional dichotomy Rad_MF(T-bar) in {1, T-bar}, which makes this one-word statement equivalent to full MF radical; this is the open non-MF branch.
  lifted-thompson-t-center-has-relative-t: that asks for every cnd function to be bounded on the centre, a Hilbert-space rigidity statement against the Haagerup property; this asks for every norm-corona representation to kill the centre, which is an approximation statement, and neither is known to imply the other.
  property-t-free-torsion-free-fp-non-mf-seed: that asks for some torsion-free finitely presented non-MF group; this names one candidate, which by the dichotomy would even have full radical.
---

**OPEN.**  Let `T̄` be the lift of Thompson's `T` to `R`, and let
`z(x) = x+1`.  Claim:

```text
z in Rad_MF(T̄),
```

that is, `pi(z) = 1` for every homomorphism `pi : T̄ -> U(prod M_n / sum M_n)`.
The proof must not use Property `(T)`, a Kazhdan subgroup, a Kazhdan
projection or Kazhdan transport.

## Equivalent forms and consequences

All of these are proved in `lifted-thompson-t-mf-radical-dichotomy`.

- **Equivalent forms.**  "`T̄` is not MF", "`Rad_MF(T̄) != 1`" and
  "`Rad_MF(T̄) = T̄`".
- **Torsion-free seed.**  `T̄` is finitely presented and torsion-free, so this
  claim gives `property-t-free-torsion-free-fp-non-mf-seed` (route
  `property-t-free-seed-via-lifted-thompson-t`).
- **Thompson's `T` and `V` are not MF.**  This claim implies `Rad_MF(T) = T` and
  `Rad_MF(V) = V`.  The latter is the single hole of the wave-15 Leavitt
  route, which puts `V` inside the binary-Leavitt Steinberg group and pushes
  its radical forward.  It was posted on the live bus as
  thompson-v-is-not-mf and as thompson-v-has-full-mf-radical.
- **Both deep inputs at once.**  So one statement feeds both deep inputs of
  `property-t-free-manuscript-results`: the binary-Leavitt collapse and the
  torsion-free seed.
- **`2V` is not MF.**  By `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`,
  `T̄ <= C(C,Z) ⋊ V <= 2V`, and a subgroup of an MF group is MF.

## How it fails

This claim is false as soon as any one of the following holds:

- `T` is MF;
- `C_T(r_k)` is MF for one `k >= 0`, where `r_k` is the rotation by `2^(-k)`
  (item 3 of the dichotomy);
- `C(C,Z) ⋊ V` or `2V` is MF.

So it is at least as strong as "`T` is not MF", which is itself stronger
than "`V` is not MF".  It is a hole that can fail on its own, and it shares no
node with the Higman cone, the abelianized-cover hole or the
virtual-torsion corner.

## What a proof must supply

- `T̄` is perfect and has no nontrivial finite-dimensional unitary
  representation.  A finite-dimensional image would be a finitely generated
  linear group, hence residually finite, and `T̄` has no proper finite-index
  subgroup (`lifted-thompson-t-perfect-centre-cubically-elliptic`).  So
  `Rad_fd(T̄) = T̄` holds for free, and all the content is in the transport
  from exact to approximate representations.
- By `compression-defect-dies-in-mf-under-mark-stability`, fd point-norm
  stability of `T̄` at one element of a nontrivial compression-centralizer
  defect would suffice.  Stability of `T̄` is not known.
- Central fibres do not help directly.  A corona representation makes `pi(z)`
  central in `B = C*(pi(T̄))`.  The fibres `B/(pi(z) - mu)` over the spectrum
  of `pi(z)` are arbitrary C-star quotients, not corona subalgebras, so
  `Rad_MF(T) = T` cannot be applied fibrewise.  Nontrivial `mu`-twisted
  representations of `T` exist on Hilbert space for every `mu` in the
  circle: the Bloch decomposition of the Koopman representation of `T̄` on
  `L^2(R)`.  So no fibrewise argument that holds in `B(H)` can force
  `pi(z) = 1`.

## Attempts

**Chromatic-code route with a non-central mark (2026-09-19,
swarm-0917-w17-w17-ptm-last1).**

- **New route.**  `lifted-thompson-t-not-mf-via-chromatic-code` has one open
  leaf, `lifted-thompson-t-bounded-area-chromatic-code`.  Its other inputs,
  `infinite-chromatic-commutator-code-kills-mf-mark` and the dichotomy, are
  ESTABLISHED.
- **Marking `z` is dead** (`central-marks-escape-chromatic-codes`).
  - Commutator codes: the invariant is the translation number.  `[F,G] = z^m`
    makes `FG = z^m GF` conjugate to `GF`, so `m = 0`.  Proofs die at CCC1.
  - Conjugacy-difference codes: the invariant is the Cayley graph of a
    finite conjugacy class, which gives `chi <= 2|C| + 1`.  Proofs die at
    CDC2, in any group.
  - Lifting codes from `T` preserves exactness but not area.
- **Exact skeleton, literal words dead**
  (`lifted-thompson-t-exact-wandering-commutator-table`).
  - Wandering copies of `F` under `x0` give an exact `K_Z` table with a
    non-central mark.
  - The literal shift words have CCC2 area at least
    `(4|m-n| - 2(|c0| + |h0|)) / P`, by a bridge count in van Kampen diagrams.
  - Bounded area needs non-literal words, presumably using the rotation and
    cone relators of `T̄`.
