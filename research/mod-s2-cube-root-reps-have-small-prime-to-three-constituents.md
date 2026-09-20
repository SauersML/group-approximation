---
rg: 2
id: mod-s2-cube-root-reps-have-small-prime-to-three-constituents
kind: claim
title: If honest representations of Mod(S_2) put a separating twist arbitrarily near a cube-root scalar, then some of them have a Torelli constituent of dimension prime to three and small compared with 1/eps
distinct_from:
  mod-s2-near-scalar-reps-reduce-to-torelli-abelian: that asks for near-cube-root representations whose Torelli constituents all have dimension 1; this asks only for one constituent of dimension n prime to three with n eps -> 0. That claim implies this one.
  mod-s2-prime-to-three-torelli-constituents-are-large: that proves n arcsin(eps/2) >= pi d_inf for such constituents; this asks that n arcsin(eps/2) can be made small, and together with d_inf > 0 the two contradict each other, which is how they prove the gap.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: under d_inf > 0 this claim is equivalent to that gap; without d_inf > 0 it is a statement about the Torelli-constituent structure of hypothetical counterexamples.
---

**OPEN.** Notation of `mod-s2-prime-to-three-torelli-constituents-are-large`. The claim (SB) is

```text
1/3 in Z_hon   implies   inf { n_i * arcsin(eps(rho)/2) } = 0 ,
```

where the infimum runs over honest `rho` with `eps(rho) = ||rho(t_s) - omega I|| < 2`, and over their Torelli
constituents `sigma_i` with `3` not dividing `n_i`.

## Position in the graph

- **With (TAP) it gives the gap.** Route `mod-s2-opnorm-torelli-gap-via-small-constituents`: (PC5) of the
  established node shows the gap is equivalent to (TAP) and (SB).
- **Implied by** `mod-s2-near-scalar-reps-reduce-to-torelli-abelian` (constituents of dimension 1). It is also
  implied by the gap, vacuously. Neither implication is filed as a route, so the graph stays acyclic.
- **How it can fail on its own.** `1/3 in Z_hon`, but along every near-`omega` family each Torelli constituent
  of dimension prime to three has dimension at least `c/eps`, and the remaining constituents have dimension
  divisible by 3. This is exactly the region that (PC6) shows no determinant argument can exclude.
- **What it does not need.** No constituent of dimension divisible by 3 has to be controlled, and nothing is
  asked about multiplicities, block stabilizers or the image of `rho`.

## Known

- *Finite image.* If `1/3` is approached by finite-image honest representations, (SB) holds for them with
  `n = 1`, by `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`.
- *Determinant tests.* Void on this claim, by (PC6).

## Attempts

- **2026-09-19, swarm-0917-w16-w16-deligne-pull (reframing): posed; the determinant attack dies by
  construction.**
  - The obvious attack on either side uses constituent determinants. By (PC6) of
    `mod-s2-prime-to-three-torelli-constituents-are-large`, they retain only `n_i mod 3` and the product `n_i h`.
  - They cannot tell a family with small prime-to-three constituents from one whose constituents all have
    `3 | n` or `n >= c/eps`. So they neither prove nor refute (SB).
  - Next test, not run: compute the Torelli-constituent dimensions of the near-scalar Jones/TL_6 points of
    `mod-s2-jones-rectangular-separating-twist-spectrum`, and of their tensor words. That would show which side
    of (SB) the known infinite-image examples fall on. Those points are near `mu_5`, not near `omega`, so they
    calibrate the dimension pattern only.
- **2026-09-20, swarm-0917-w22-w22-deligne-pull (group-rings): (SB) is equivalent to the Torelli-abelian
  reduction; it is not weaker.** See `mod-s2-small-constituents-collapse-to-torelli-abelian-reduction`
  (ESTABLISHED, unreviewed).
  - *Identity.* Let `W` be an irreducible `H`-subrepresentation of some tensor word `V_ab`. Call it admissible
    if `3 not| (a - b) dim W`, with weight `(a + b) dim W`.
    - The tensor-word loss `D(rho)` of `mod-s2-near-scalar-torelli-closure-dichotomy` equals the least weight
      of an admissible `W`.
    - Invariant: `Lambda^(dim W) W` is an `S`-invariant line in `V_(a dim W, b dim W)`.
    - With (CD3) and (TA1), every admissible `W` then has `(a + b) dim W * eps >= 2 sin(pi d_inf)`.
  - *Collapse.* (SB), its tensor-word version and `mod-s2-near-scalar-reps-reduce-to-torelli-abelian` are
    equivalent.
    - So (PC5) "gap iff (TAP) and (SB)" is the tautological split.
    - The route `mod-s2-opnorm-torelli-gap-via-small-constituents` has the same open content as the
      finite-index-multiplier route.
    - The region under "How it can fail on its own" above is exactly the failure region of the reduction.
    - The implication (SB) implies reduction is filed as route
      `mod-s2-torelli-abelian-reduction-via-small-constituents`.
  - *Class killed.* Constituent-dimension arguments, which locate a small admissible constituent in `rho`, a
    Schur functor, a tensor word, or a sub- or quotient representation of these, die at the step
    "`D(rho) eps -> 0`". That step is the reduction itself.
  - *Next test run (calibration).* On Jones' family with `x/pi` irrational, every irreducible `H`-constituent
    of every tensor word on which `zeta I` acts non-trivially has dimension divisible by 5, while
    `eps_zeta -> 0`. So the known infinite-image examples lie entirely on the failing side of the fifth-root
    analogue of (SB). The fifth-root reduction holds only through the external character `chi_zeta`.
  - *Status.* OPEN. It is now literally the reduction. Surviving attacks are (R-a) by an input that separates
    `omega` from `mu_5`, (R-b) by non-dimension data, or (TAP).
