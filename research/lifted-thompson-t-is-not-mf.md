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

- **2026-09-20 (swarm-0917-w23-w23-ptl-pull, transplanter via symbolic-dynamics):
  twist-and-cut; the residual is full-circle rigidity; the target stays OPEN.**
  - *Established* `lifted-thompson-t-corona-centre-spectrum-is-full-circle`, an
    implication.  Assume the T gap `G(eps_0)`, which is equivalent to
    `thompson-t-has-full-mf-radical`.  Put `alpha_0 = min(pi, 24 arcsin(eps_0/2))`.
    - *Central twist.*  If `sp(rho(z))` lies in an arc of half-width `alpha < alpha_0`, then
      untwisting by `u = rho(z)^(1/12)` gives an exact `Z/4 * Z/3` pair with
      `r_1 = r_2 = 1` and pentagon defect `||u - 1|| <= 2 sin(alpha/24)`.  So `rho` is
      trivial.
    - *Short pieces.*  Tensoring a corner with its conjugate kills every clopen piece of
      `sp(rho(z))` shorter than `alpha_0`.
    - *Dilation.*  The dilation `lambda` (`t_(k+1)^2 = t_k`) spreads the remaining arcs.
    - *Result.*  Every nontrivial corona representation has `sp(rho(t_k)) = S^1` at
      every level `k`, in every commutant corner it moves, and levelwise along every
      subsequence on which it stays nontrivial.
  - *Reduction.*  The target is equivalent to `thompson-t-has-full-mf-radical` plus
    (FC): no nontrivial corona representation has full-circle centre in all of these
    senses.  This sharpens the "Where it already holds" paragraph of
    `lifted-thompson-t-centre-has-commutant-eigencorners`, where "perfect away from 1"
    becomes "the whole circle".
  - *Class killed: central functional-calculus twists and cuts.*  These are twists or
    cuts of `rho` made with the functional calculus of `rho(z)`, of `rho(t_k)`, or of
    tensor powers `rho^(⊗p) ⊗ conj(rho)^(⊗q)`.
    - *Invariant.*  The degree vector `(1,...,1,-1,...,-1)` of the centre on the joint
      spectrum `(S^1)^(p+q)` is not divisible by 12.
    - *Failure step.*  The twelfth root `u` with `u^12 = rho(z)` does not exist.  The
      residual exponent in `(B'A')^5 = u^(36-35)` is the Euler number 1.
    - *Where the class dies.*  Exactly on (FC).  A witness for (EC) must come from
      commutant projections outside `C^*(rho(t_k))` and its tensor powers.
  - *Next falsifiable step.*  Decide whether an (FC) representation can exist.  A
    candidate for building one is a sequence of exact pairs in which the spectrum of
    `(BA)^5` equidistributes on the circle while the defect of `r_1` and `r_2` tends to 0.
    Such a sequence would refute the T gap and settle `thompson-t-has-full-mf-radical`
    negatively.  Conversely, no (FC) representation exists at all if the T gap holds with
    every corner forced to be a scalar.
