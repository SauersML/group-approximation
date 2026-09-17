---
rg: 2
id: kl-amenable-regular-roots-lie-in-the-coefficient-group
kind: claim
title: Over a finite coefficient group a Fox root generating a finite or amenable group other than the coefficient group is never regular, and at every infinite root the l2-kernel of the Fox derivative has dimension at least 1/|F|
distinct_from:
  kl-regular-roots-lift-through-locally-indicable-kernels: that proves regular roots inject locally indicable extensions and names one blind family (words conjugate to t^m c); this proves where regular roots cannot be, for every word over a finite group, and yields a blind word not of that form whose every root is singular.
  kl-p-power-index-reduces-to-p-nonsingular-square-systems: that uses roots inside Q = G/H with an invertible matrix mod p and stops at an open systems problem; this is a non-existence statement about roots outside Q, proved by an Euler characteristic count on the coset graph.
  kervaire-laudenbach-holds-for-hyperlinear: that proves injectivity for hyperlinear coefficients by topology of unitary groups; this is an obstruction to one certificate, and its l2 part says that operator (von Neumann dimension) injectivity of the Fox derivative never holds at infinite roots.
artifacts:
  - experiments/kl-regular-roots-2026-09-17/cosetbound.py
  - experiments/kl-regular-roots-2026-09-17/cosetbound.out
  - experiments/kl-regular-roots-2026-09-17/regroots.py
  - experiments/kl-regular-roots-2026-09-17/certify.py
  - experiments/kl-regular-roots-2026-09-17/driver5.py
  - experiments/kl-regular-roots-2026-09-17/driver5.out
  - experiments/kl-regular-roots-2026-09-17/euclid.py
  - experiments/kl-regular-roots-2026-09-17/driver6.py
  - experiments/kl-regular-roots-2026-09-17/driver6.out
---

Notation of `kl-regular-roots-lift-through-locally-indicable-kernels`: `F` a
group, `w-` a word in `F * <t>` of degree `m != 0`, a root `(Gamma, tau)` with
`w-(tau) = 1`, and `D in Z[Gamma]` the Fox derivative at `tau`. The root is
regular over a ring `R` if `mu D = 0`, `mu in R[Gamma]`, forces `mu = 0`.
Regularity in `Gamma` is the same as regularity in `Gamma_0 = <F, tau>`
(split `mu` along left cosets of `Gamma_0`). So we take `Gamma = <F, tau>`.

Let `F` be **finite**.

1. **Coset complex.** The maps
   `Z[Gamma] --(mu -> mu D)--> Z[Gamma] --(x -> x(tau - 1)F)--> Z[Gamma/F]`
   of left `Z[Gamma]`-modules compose to zero, and the second has image the
   augmentation ideal of `Z[Gamma/F]`.
2. **Finite roots.** If `Gamma` is finite and `Gamma != F`, then over every
   field `k` right multiplication by `D` on `k[Gamma]` has rank at most
   `|Gamma| - [Gamma:F] + 1 < |Gamma|`. So the root is regular over no field,
   over neither `Z` nor any `F_p`.
3. **Infinite roots: l2-kernel.** If `Gamma` is infinite, the kernel of right
   multiplication by `D` on the group von Neumann algebra `N(Gamma)` has von
   Neumann dimension at least `1/|F|`. So `D` is never l2-injective.
4. **Amenable roots.** If `Gamma` is infinite and amenable, `D` has a nonzero
   left annihilator in `Z[Gamma]`, and hence in `F_p[Gamma]` for every `p`.
5. **Consequence.** A root generating an amenable group is regular (over `Z`,
   resp. over `F_p`) iff `tau = c in F` and `D` is a unit of `Q[F]` (resp.
   `F_p[F]`). If `Gamma_F = (F * <t>)/<<w->>` is amenable and different from
   `F`, then every root of `w-` generates a quotient of `Gamma_F` (hence
   amenable), item 1 of the lifting claim applies only through roots in `F`,
   and `K(F,1) ∪ e^1_t ∪ e^2_(w-)` is not aspherical.
6. **A blind word.** For `F = C_6 = <c>` the word
   `w- = c^2 t^(-1) c^5 t c^5 t^(-1) c` (degree `-1`) has no regular root over
   `Z` or any `F_p` in any group. Here `Gamma_F ≅ B_3/<<sigma_1^6>>`, a
   cyclic central extension of the Euclidean `(2,3,6)` triangle group, hence
   amenable. Its only root in `F` is `c`, with `D = 1 - c - c^5`, which vanishes
   at the character `c -> e^(i pi/3)`. Unlike the family `t^m c`, this word is
   not conjugate to a monomial in `t`.

## Why it matters for the lane

The regular-root certificate of the lifting claim is the only route recorded on
this lane that handles torsion quotients `G/H` which are not `p`-groups. Item 5
kills every *amenable* instance of that route beyond the roots in `F`, which the
p-power-index node already records. Item 3 kills the natural non-amenable
strategy: prove that `D` is a non-zero-divisor by showing it is injective on
`l^2(Gamma)` or `N(Gamma)`, e.g. through the Atiyah conjecture or approximation
by finite quotients. That injectivity always fails. A regular root that is not
in `F` exists, if at all, only in a non-amenable group, and only as a
non-zero-divisor of `Z[Gamma]` with a nonzero l2-kernel. Such elements cannot
exist in torsion-free groups satisfying the Atiyah conjecture, but `Gamma`
contains `F`, so they are not excluded by it.

## Status

**ESTABLISHED** (proposed) through `kl-amenable-regular-roots-coset-euler-proof`.
The proof uses the Fox fundamental formula, connectivity of the Schreier coset
graph, and three facts from Lück, *L2-Invariants* (2002): additivity of the
von Neumann dimension (Thm 6.7), `dim N(Gamma) ⊗_(C Gamma) C = 0` for infinite
`Gamma` (Thm 6.54(8)), and dimension-flatness of `N(Gamma)` over `C Gamma` for
amenable `Gamma` (Thm 6.37). These are cited from memory, not pinned. Not
independently reviewed. No novelty claimed.

Checks: `cosetbound.py` verifies the vanishing in item 1 and the rank bound
of item 2 (rank modulo a large prime) on every root found for random words over
`C_2`, `C_3`, `S_3` inside `S_6`: 598 / 361 / 184 roots, all satisfy both, and
the bound is attained on 61 / 93 / 25 of them (`cosetbound.out`). `driver5.py`
certifies all 30 roots of the item-6 word in `S_8` singular exactly
(integer determinants of the permutation representations). `driver6.py` maps
the word onto `Z[omega] ⋊ C_6` through the braid coordinates
`c' = c^(-1) t^(-1) c^3` and finds `det = 0` for the `6 x 6` Laurent matrix of
`D`.
