---
rg: 2
id: weakly-bernoulli-liftable-actions-force-virtual-splitting
kind: claim
title: Over a w-rigid quotient, a liftable free action weakly contained in Bernoulli shifts exists only for virtually split finite extensions
distinct_from:
  bernoulli-lifts-across-finite-kernels-force-virtual-splitting: that is the proved exact case, for Bernoulli and other s-malleable actions, through Popa's cocycle superrigidity; this asks the same for every liftable action that is only weakly contained in Bernoulli shifts, which needs an approximate form of superrigidity.
  finite-kernel-rokhlin-ascent-from-weakly-minimal-lift: that proves ascent from such a liftable action; this would show the hypothesis there is available over w-rigid quotients only in the trivial virtually split case.
---

**OPEN.** Let `N ◁ W` be finite and `Q = W/N` w-rigid in Popa's sense, for example infinite with property (T). Suppose
some free p.m.p. `Q`-action `Y_0` is the `N`-quotient of a free `W`-action, and `Y_0` is weakly contained in the
Bernoulli shift `[0,1]^Q`. Then the extension splits over a finite-index subgroup of `Q`.

**Why it matters.**
- For Deligne's triple cover, it would rule out case (i) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`.
  Only `seward-direct-product-relative-rokhlin-entropy-conjecture` would remain as a known sufficient condition for
  `rokhlin-maximality-ascends-finite-normal-extensions` over `Sp_4(Z)`.
- A counterexample would be a liftable action weakly equivalent to Bernoulli over a rigid base with a persistent
  class. By Corollary C, that would make the extension Rokhlin-maximal: a Rokhlin lower bound over a group whose
  soficity is open.

**Reformulation (partly sketched).**
- **Proved direction.** If the twisted section action satisfies `Ω/N ≺ [0,1]^Q`, the hypothesis holds with `Y_0 = Ω/N`.
- **Sketched converse.** Given a lift `X_0 -> Y_0`, the map `x -> (v -> τ(vx))` sends `X_0` equivariantly to the
  section space, with some invariant measure. Joining with independent uniform `N`-labels should give the uniform
  measure, and so `Ω/N ≺ Y_0 × N^Q ≺ [0,1]^Q`. This is not written out.

Either way, the claim asks about measurable almost-lifts of the extension cocycle on the Bernoulli orbit relation:
maps `c : T × X -> W` with `π(c(t, x)) = t` and the cocycle identity outside small measure, for each finite `T`.

## Attempts

- **Exact lifts (ex-rokhlin-ascent-finite-kernel, 2026-09-13).** Proved: exact lifts on s-malleable actions force
  virtual splitting (`bernoulli-lifts-across-finite-kernels-force-virtual-splitting`). The proof runs Popa's
  superrigidity on the lifting cocycle, then an invariant probability measure on `Q` for the twisted conjugation.
- **Where it dies.** Weak containment supplies only almost-cocycles on finite sets `T` with small defect.
  - Popa's deformation/rigidity argument starts from an exact cocycle, so it yields nothing here.
  - No stability theorem for almost-cocycles of Bernoulli actions into countable groups was found in the sources read
    (arXiv:math/0512646 read at the theorem-statement level only).
  - The degree-two analogue that works for finite actions is Gohla–Thom's cosystolic inequality
    (`gohla-thom-stable-base-nonsofic-extension`). It is a higher-dimensional expansion hypothesis, not property (T),
    and it concerns finite actions rather than Bernoulli shifts.
- **Normed reformulation, a (T) base where it holds, and the Sp_4(Z) instance (ex2-rokhlin-almost-cocycle,
  2026-09-13).** All for central finite kernels over type-F bases; the noncentral case is untouched.
  - **Reformulation.** `bernoulli-maximizes-extension-class-norm`: a liftable weakly Bernoulli action exists iff the
    Gohla--Thom norm of the extension class on `[0,1]^Q` is 0, and Bernoulli has the largest norm among free actions.
    So this claim says the class is nonzero in reduced cohomology of the Bernoulli shift. Popa gives only unreduced.
  - **Holds over p-adic lattices.** `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`: the claim holds over
    torsionfree lattices in `PSp_2d(Q_p)`, `d >= 4`, large `p`, with their Prasad--Deligne extensions. This is a
    corollary of Gohla--Thom 2.16 and 3.4.
  - **Sp_4(Z).** `deligne-triple-cover-no-weakly-bernoulli-liftable-action` is open. It follows from
    `deligne-class-congruence-cosystole-bounded-below`, and also from nonsoficity of `E_3` by
    `weakly-bernoulli-liftable-action-makes-extension-sofic`.
  - **Where it dies in general.** Popa plus compactness excludes exact trivializations of every bounded block
    complexity, but not sequences of growing complexity. A uniform dimension-2 expansion input is needed, and property
    (T) supplies only dimension 1.
- **Positive polarity without rigidity (ex2-rokhlin-liftable-positive, 2026-09-13).** Settled over non-rigid bases
  by `weakly-bernoulli-lifts-over-amenable-free-product-bases`.
  - Over an infinite amenable `Q`, every quotient `X/N` of a free `W`-action is liftable and weakly equivalent to
    Bernoulli.
  - Over `Q_p * Z`, built from the Abels--Prüfer quotient, the non-residually-finite central extension
    `Γ_p *_C (C × Z)` carries a liftable action weakly equivalent to Bernoulli. The base is non-amenable and has
    no (T).
  - So some rigidity hypothesis is needed. Non-amenability, failure of (T), or a persistent class alone are not
    enough.
  - Exact lifts exist on every treeable free action (`treeable-free-actions-lift-across-finite-normal-extensions`).
  - The question is exactly almost-lifts on Bernoulli (`weakly-bernoulli-lift-iff-bernoulli-almost-lifts`), and
    the positive polarity passes to subgroups.
  - The first undecided non-rigid base is `deligne-sl2-z-1-p-weakly-bernoulli-lift`.
- **Toledo's examples checked from the source (same lane).** D. Toledo, Publ. IHES 77 (1993) 103--119, pp. 103--105.
  - The groups are `π_1(M − D)`, where `M` is a compact locally symmetric variety for `SO(2, n)` with `n >= 4` even,
    and `D` is a smooth totally geodesic divisor. Quoted: "each example admits a surjective homomorphism to a
    lattice in the Lie group SO(2, n) whose kernel is a free group of infinite rank".
  - Residual finiteness fails because the groups contain the fundamental group of the boundary of a tubular
    neighbourhood of `D`. Quoted: "a co-compact lattice in a certain covering group of SO(2, n − 1)". It is not
    residually finite by Raghunathan's Main Theorem.
  - That subgroup is a central extension of a cocompact lattice in `SO(2, n − 1)` with `n − 1 >= 3`. That group
    has real rank 2, so it has property (T) by Kazhdan's theorem (not imported as a node).
  - Toledo's group itself is not a finite central extension of anything.
  - **Verdict.** Toledo supplies no base without (T), so the predecessor's recollection does not fit. The Nori
    and Catanese--Kollár branched-cover examples mentioned on p. 105 rest on the same Raghunathan input.
