---
rg: 2
id: one-ended-shell-inputs-admit-no-shift-normalizing-enumeration
kind: claim
title: For a one-ended input no nonzero power of the cofinite shift normalizes the regular near copy
distinct_from:
  shell-prefix-core-detects-finite-ray-enumerations: that classifies when a power of the shift COMMUTES with every input permutation near infinity (the identity endomorphism), for every input; this excludes conjugation by a shift power into the regular copy through ANY endomorphism, for one-ended inputs.
  shell-germ-fp-is-an-ascending-hnn-gate: that makes germ finite presentation equivalent to finite presentation of R_nu plus an ascending union of shift conjugates of a finitely generated B in ker(eta); this shows B = lambda(P) never works for one-ended inputs, so any witness must be strictly larger.
  rational-regular-shell-actions-require-virtually-cyclic-input: that excludes finite-state regular shell actions; this excludes a group-theoretic normalization at the level of near permutations, whatever the complexity of nu.
artifacts:
  - research/artifacts/shell-envelope-general-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty
claimed).

Let `P` be a finitely generated one-ended group with finite generating set
`S`, and let `nu: P -> N` be any bijection. Write `lambda_g(nu(h)) = nu(gh)`
for the regular permutations transported to `N`, and `s: n -> n+1`. Fix an
integer `m != 0`. Then there is no map `phi: S -> P` such that, for every
`g` in `S`,

    s^m lambda_g s^-m = lambda_(phi(g))   near infinity,

meaning the two sides agree at all but finitely many `n`.

Consequences, for the near shift group `R_nu = <lambda(P), s>` of
`shell-germ-group-has-index-two-fiber-product`:

1. `s^m lambda(P) s^-m` is not contained in `lambda(P)`, for any `m != 0`
   and any enumeration. For `m > 0` this says the shift never conjugates the
   regular copy into itself.
2. In `shell-germ-fp-is-an-ascending-hnn-gate`, the subgroup `B = lambda(P)`
   never witnesses the ascending condition. In particular `ker(eta)` is
   never the regular copy `lambda(P)` itself.
3. Through the parity fiber product, where `tau^2` corresponds to `(s,s)`
   and `rho_g` to `(lambda_g, 1)`, no nonzero even power of `tau`
   normalizes `rho(P)` in the shell germ group `Q`.

One-ended inputs include:
- every direct product of two infinite finitely generated groups, which
  covers the route inputs `P_0 x Z`;
- BS(1,2);
- Z wr Z;
- Z^2.

These are standard facts, not re-proved here.

The one-ended hypothesis cannot be dropped. For the two-ended input
`P = Z`, use the zigzag enumeration
`nu(0)=0`, `nu(k)=2k-1`, `nu(-k)=2k` for `k>=1`. Then
`s lambda_1 s^-1 = lambda_(-1)` near infinity.

This does not exclude the ascending gate with a larger `B`, and it says
nothing about finite presentation of `E_nu`. Inputs with infinitely many
ends are not treated.

DERIVATION
one-ended-shell-shift-normalization-proof
