---
rg: 2
id: sp4-shifted-maslov-multipliers-stay-far-on-finite-index
kind: claim
title: Small Torelli transgression classes cannot move the cube-root Maslov multiplier of Sp4(Z) into the finite-dimensionally realizable classes of any finite-index subgroup
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that bounds the realizable classes of the whole lattice Sp4(Z); this asks for a gap uniform over ALL finite-index subgroups, after a shift by a small transgression class that need not come from Sp4(Z).
  deligne-triple-cover-fd-central-invisibility: that is the unshifted statement on Gamma itself (h = 0, Gamma' = Gamma); this allows passing to finite index and shifting by small non-constant Torelli functions.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is about all honest representations of Mod(S_2); this is its Torelli-abelian part, rewritten as pure Sp4(Z) cohomology by mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: its (E4) gives level-by-level floors that degenerate with the level; this asks for one floor for every finite-index subgroup.
---

**OPEN.** Notation (`X`, `A`, `a`, `b`, `r`, `Phi_(Gamma')`, fd-realizable) as in
`mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers`.

**Statement (D).** There is `eta_0 > 0` such that for every finite-index `Gamma' <= Sp_4(Z)`, every
`Gamma'`-invariant `h : X -> (-eta_0, eta_0)` and each sign,

```text
Phi_(Gamma')(h)  -+  (1/(3r)) [b|_(Gamma')]      is NOT fd-realizable on Gamma'.
```

## Position in the graph

- **Equivalent to the Torelli-abelian gap.** By the established dictionary
  `mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers`, (D) holds iff `1/3` is not in `Z_ab`.
  Conjugating `u` and replacing `h` by `-h` swaps the signs, so one sign suffices.
- **Necessary for the flagship.** If (D) fails, then `1/3 in Z_ab <= Z_hon <= Z_op`, and by (U4) of
  `mod-s2-real-untwisting-identifies-deligne-norm-parameters` `deligne-triple-cover-exact-mf-radical` fails.
  This is not filed as a route, to keep the graph acyclic.
- **Sufficient for the Torelli-abelian part of `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.**
  The remaining part is `mod-s2-near-scalar-reps-reduce-to-torelli-abelian`. The finite-image part of that
  reduction is established in `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`.

## What is known

- **Gamma' = Gamma.** `X` is one `Gamma`-orbit, so a `Gamma`-invariant `h` is a constant `c`. Then
  `h o a = c sigma o a = (c/r)(dF - b)` (Step 1 of the dictionary proof), so `Phi_Gamma(c) = -(c/r)[b]`. The condition
  becomes realizability of the Maslov-circle point `-((1/3 + c)/r)[b]`. By
  `sp4-fd-projective-multiplier-is-finite`, the circle meets the realizable set only in classes of order at most 2.
  So (D) at `Gamma' = Gamma` reduces to `1/3` not being in the finite set of such parameters, which is the
  content of `deligne-triple-cover-fd-central-invisibility`. This case is a sketch assembled from those nodes and is not
  separately filed.
- **Finite dimension of the search space at a fixed level.** `Gamma'` has finitely many orbits on `X`, so
  `h` ranges over a finite-dimensional space and `Phi_(Gamma')` has finite-dimensional image in `H^2(Gamma';R)`.
  If `R(Gamma')`, the set of realizable classes of `Gamma'`, is finite, then each single level has a floor
  `eta(Gamma') > 0`. That finiteness is expected from superrigidity plus the congruence subgroup property, as
  in `sp4-fd-projective-multiplier-is-finite`, but it is not checked here. The whole difficulty of (D) is that
  the floor must be uniform in `Gamma'`.

## Attempts

- **2026-09-18, swarm-0917-w10-w10-deligne-pull: corestriction gives only a non-uniform constraint.**
  - *Idea.* Tensor induction sends a `d`-dimensional projective representation of `Gamma'` with class `c` to a
    `d^n`-dimensional projective representation of `Gamma` with class `cor(c)`, where `n = [Gamma : Gamma']`.
    This is the standard multiplier formula for tensor induction; it is not source-verified here.
  - *Computation.* `cor o res = n`. Also `cor Phi_(Gamma')(h) = Phi_Gamma(tr h)`, where
    `tr h = sum_i g_i . h` is `Gamma`-invariant, hence constant, equal to `n m(h)` with `m(h)` the mean of `h`
    over a transversal. So (TA2) on `Gamma'` forces `-(n (1/3 + m(h))/r)[b]` to be realizable on `Gamma`.
  - *Death.* By FM1 this confines `n(1/3 + m(h))/r` to a discrete set. But `n` is unbounded and `m(h)` is small
    and continuous, so the constraint is non-uniform. When `3` divides `n`, the cube-root part drops out entirely.
    Any test that factors through corestriction to `Gamma` only sees `n(alpha + m(h))`, so it cannot give a floor
    uniform over finite-index subgroups.
  - *What survives.* A proof of (D) must use classes of `H^2(Gamma';R)` that are not restrictions from `Gamma`,
    the directions `Phi_(Gamma')(h)` can reach, or a uniform control of `R(Gamma')` as `Gamma'` shrinks.
    Transgression pairing, if it is correct: for a 2-cycle `z` of `Gamma'`, `<Phi(h), z> = h(kappa'(z))`, where
    `kappa' : H_2(Gamma') -> A_(Gamma')` is the 5-term-sequence transgression of the extension. So the reachable
    directions are dual to the Torelli classes that the second homology of `Gamma'` hits. This is not checked here.
