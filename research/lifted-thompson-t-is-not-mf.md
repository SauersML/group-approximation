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

- **2026-09-20 (swarm-0917-w22-w22-ptm-pull, transplanter /
  entropy-measure): tracial methods reach a sharp dichotomy and then die at
  a named norm-only conjunct.**

  *Transplant tried.*  Push entropy, measure and character arguments
  (normalized traces, ultralimit states, HS defects) through the centre of
  `T̄`.  The first form was "`Res_hyp(T̄) = T̄` iff `T` is not hyperlinear".
  It is not new: it follows at once from the normal-subgroup structure of
  `T̄` and Thom's central-quotient descent (Remark 3.4 in
  `thom-central-corner-criterion`).  It is not recorded as a node.

  *What survived (new, ESTABLISHED).*  `lifted-thompson-t-shadow-residual-dichotomy`:
  - `S(T̄) = R_(infinity->2)(T̄)` is `1` or `T̄`, by the dilation argument of
    the MF dichotomy run on the shadow residual.
  - `T` MF implies `T̄` hyperlinear, hence every Euler-twisted
    `L_(s·eu)(T)` is Connes-embeddable.  One gapped commutant corner of
    `rho(z)` already gives the same conclusion.
  - On the branch `S(T̄) = T̄`, three things hold for every corona map:
    it is a full-trace padding; every commutant corner is HS-invisible in
    its renormalized ultralimit traces; and `sp(rho(z) P)` is connected and
    contains `1` for every nonzero commutant corner `P`, and likewise for
    every `t_k` via `rho ∘ lambda^k`.

  *New exact decomposition.*  `lifted-thompson-t-not-mf-via-gapped-corners`:

  ```text
  this claim  <=>  lifted-thompson-t-shadow-residual-is-full (A, tracial)
                   AND lifted-thompson-t-centre-has-gapped-commutant-corners (EC′, norm only)
  ```

  (EC′) is implied by the eigencorner conjunct (EC) of
  `lifted-thompson-t-not-mf-via-central-eigencorners`, so it is weaker.
  (A) is stronger than `thompson-t-has-full-mf-radical`.

  *Death step (the obstruction for the whole family).*  Every tracial
  invariant (entropy, trace, spectral measure of `rho(z)` for an ultralimit
  trace, character) sees only `S(T̄)`.  So a tracial argument proves at most
  (A).  Under (A), a counterexample `rho` has these properties:
  - it is HS-invisible in every commutant corner;
  - the spectrum of `rho(z)` in every corner is a connected arc through `1`;
  - no approximate corner has error below `|lambda - 1|`.

  This is exactly the configuration of
  `o2-suspension-central-unitary-evades-commutant-corners`.  No ultralimit
  trace of any corner distinguishes `rho` from the trivial representation.
  So the family dies at conjunct (EC′), which is invisible to every
  invariant that the family computes.  It also shows that the w16 cut
  inside `C^*(rho(z))` (on
  `lifted-thompson-t-centre-has-commutant-eigencorners`) never starts under
  (A): the whole of `sp(rho(z))` is then one arc through `1`.

  *Calibrations.*
  - **Modular subgroup.**  The preimage of `PSL(2,Z) <= T` in `T̄` is
    `B_3 = <a, b | a^2 = b^3>`.  Here `a` and `b` lift the generators of
    orders 2 and 3, and `a^2 = b^3 = z = Delta^2`.  `B_3` has the character `sigma_i -> e^(i theta)`,
    which sends `z` to `e^(6 i theta) != 1`.  So no argument that restricts
    to the modular subgroup can succeed; it must use the relators that make
    `T̄` perfect.
