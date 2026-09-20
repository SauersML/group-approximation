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

- **2026-09-20 (swarm-0917-w23-w23-ptm-pull, transplanter / probability-random): class-kill of
  bounded-Lie-closure amplification.  Established
  `lifted-thompson-t-twisted-witnesses-need-unbounded-lie-closure`.  The target stays OPEN.**
  - *Result.*  Let `σ` be an exact representation of `K(3,4) = <x, y | x^4 = y^3>`, and let
    `N` be the dimension of the semisimple part of the Lie algebra of the closure of `σ(K)`.
    Suppose the `T̄` defect satisfies `D < min(1/2, δ_N/2)`, where `δ_N` is the untwisted gap
    of `T` over `Z4 * Z3` in dimension `<= N`.  Then `σ` is abelian, `x ↦ u^3`, `y ↦ u^4`,
    and the twist satisfies `||σ(x^4) - 1|| <= 12 D`.  The constant `12` is sharp.
  - *Device.*  `Ad ∘ σ` on the complexified semisimple part kills the centre.  So it is a
    `Z4 * Z3`-representation of dimension `N` with `T` defect `<= 2D`.  Below `δ_N` it is
    trivial, which makes the closure virtually a torus, and the virtually-solvable-image lemma
    finishes.
  - *Consequence.*  Every asymptotic representation of `T̄` with defect `→ 0` and scalar twist
    bounded away from `1` has semisimple Lie closure of unbounded dimension.  So no witness
    against this claim comes from `Sym^m` or tensor powers of a fixed compact pair, from any
    finite or virtually solvable quotient of `K(3,4)` or of the Brieskorn lattice, or from
    random models in a fixed compact group.
  - *Where it stops.*
    - The bound is only as strong as `δ_N`.  A disproof must make `T` itself nearly MF at the
      growing dimension `N` while keeping the twist.
    - Non-scalar twists need the eigencorner step (EC) first, which is still open.
  - *Evidence.*  `experiments/lifted-t-lie-closure-gap-2026-09-17/`.
    - `Sym^1` of an `SU(2)` pair gives a twisted, nonabelian `D = 2 sin(π/24)`.
    - Its `Sym^2` is an exact `SO(3)` representation of `T`'s free product with
      `D_T = 2 sin(π/12)`.  So the factor `2` of the adjoint transfer is nearly attained.
