---
rg: 2
id: formalizable-pairs-induce-polynomial-automorphisms-on-constants
kind: claim
title: A formalizable left-inverse pair acts on constant configurations by a polynomial automorphism, hence affinely over one track
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that linearizes a formal pair at a constant configuration and concludes bijectivity from direct finiteness; this specializes all site variables diagonally and concludes that the constant-configuration map is a polynomial automorphism, which obstructs formalizability itself.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that shows canonical representatives can fail to be formal for a formalizable pair; this shows some bijective pairs have no formalizing representatives at all.
  binary-left-inverse-pairs-are-formalizable: that asks whether every pair over F_2^n alphabets is formalizable; this proves that over one track F_q with q >= 4 some sitewise bijective pairs are not, so the prime-field analogue needs stabilization.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Let `q` be a prime power, `G` any group, and `(tau, sigma)` automata on `(F_q^n)^G` whose left-inverse
identity `sigma o tau = id` holds formally for some equivariant polynomial representatives `P` of `tau`
and `Q` of `sigma`, possibly on larger memories. Replace every variable `X_(h,i)` by `T_i`. Then
`p(T) = P(T,...,T)` is a polynomial automorphism of affine `n`-space over `F_q` with inverse
`q(U) = Q(U,...,U)`. On `F_q^n` it induces the constant-configuration map `c -> tau(c)(1)`.

**Consequences.**
- **One track.** For `n = 1` the constant-configuration map is affine, `t -> a t + b`.
- **Non-formalizable bijective pairs.** For `q >= 4`, a sitewise automaton applying a non-affine
  permutation of `F_q` is a bijective pair with no formalizing representatives, on every group. Over
  prime fields this happens exactly for `p >= 5`.
- **Representation matters.** `F_4` as one track has such pairs; `F_2^2` has none
  (`tame-maps-induce-every-permutation-of-prime-field-cubes`).

Proof: Section 2 of the artifact.
