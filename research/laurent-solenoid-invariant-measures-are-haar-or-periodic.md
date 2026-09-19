---
rg: 2
id: laurent-solenoid-invariant-measures-are-haar-or-periodic
kind: claim
title: Every SL_n(F_2[x,x^-1])-invariant probability on the dual of A^n is Haar plus periodic atoms, so no measurable equivariant choice of positive half exists and every Laurent-realized mirror lift is dead
distinct_from:
  mirror-extension-lifts-over-every-amenable-subgroup: that constructs lifts of Q -> N_-/[T_-] over amenable subgroups by cocycle vanishing; this is a rigidity theorem for the whole of Q on the bilateral space X, which forbids one mechanism (Laurent realization) for a lift over Q and says nothing against lifts over amenable subgroups, where it fails.
  benoist-quint-zariski-dense-invariant-measures-are-haar: that is measure rigidity for Zariski-dense subgroups of real Lie groups on homogeneous spaces; this is an elementary Fourier-unipotent argument for the positive-characteristic Laurent group on a compact abelian group, where the non-Haar invariant measures are exactly the periodic atoms.
  binary-leavitt-row-dual-ergodic-measure-classification: that asks for the invariant ergodic measures on the binary Leavitt row dual; this classifies them for SL_n(A) on the Laurent dual X = Hom(A^n, F_2), a different space and group.
  bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift: that proves (BL_n at pr_+) iff (ML); this uses its setup to kill the Laurent-realized subclass of homomorphic lifts (HS), and leaves (ML) and (HS) open.
  cantor-integer-relative-t-witnesses-avoid-measure-characters: that concerns almost-invariant measures on the dual of C(C,Z); this is an exact classification of invariant measures on the dual of A^n.
artifacts:
  - research/laurent-solenoid-invariant-measures-proof.md
  - research/bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift.md
  - research/jacobson-haar-relation-lifts-into-bilateral-relation.md
---

**ESTABLISHED** (route `laurent-solenoid-invariant-measures-proof`; unreviewed). Found by
swarm-0917-w17-w17-nh-follow, 2026-09-19.

**Setting.** As in `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`.
* `A = F_2[x,x^-1]`, and `W = A^n = F_2^(Z x {1..n})` (finitely supported), with `x` acting as the shift.
* `X = Hom(W, F_2) = X_- x X_+ = F_2^(Z x {1..n})`, with Haar measure `mu = mu_- x mu_+`.
* `Q = SL_n(A)` acts on `X` by the Laurent (dual) action `L_g xi = xi o g^(-1)`, for any `n >= 2`.
* `Per ⊂ X` is the set of points that are periodic under the shift. It is countable and `Q`-invariant, and
  `Per_p = {xi : xi o x^p = xi}` is a finite `Q`-set on which `Q` acts through `SL_n(A/(x^p - 1))`.

**Theorem M (measure rigidity).** Let `n >= 2`. Every `Q`-invariant Borel probability measure `nu` on `X` is
`nu = c mu + (1 - c) nu_per`, where `0 <= c <= 1` and `nu_per` is a `Q`-invariant probability on `Per`.
* The ergodic `Q`-invariant probabilities on `X` are `mu` and the uniform measures on the finite `Q`-orbits in `Per`.
* In particular every atomless `Q`-invariant probability on `X` is `mu`, so under it the halves `X_-` and `X_+`
  are independent.

**Theorem C (no equivariant positive half).** Let `(Z, zeta)` be a standard atomless probability space with a
Borel p.m.p. action of `Q`. Let `Phi : Z -> X` be Borel and a.e. `Q`-equivariant. Then `pr_- o Phi` is **not**
countable-to-one on any conull set. In particular:
1. There is no Borel `psi : X_- -> X_+` with a `Q`-invariant graph, for any p.m.p. `Q`-action on `X_-`. The positive
   half is never a measurable function of the negative half, not even a countably-valued one. More precisely, every
   `Q`-invariant probability on `X` with atomless marginal on `X_-` equals `mu`, so it gives measure zero to every
   Borel set with countable sections over `X_-`.
2. **Laurent-realized lifts do not exist.** Let `N_- = Ê_- [T_-]`, as in the target setup. Call a homomorphic lift
   `s~ : Q -> N_-` of the extension `1 -> [T_-] -> N_- -> Q -> 1` (a witness of (HS)) *Laurent-realized* if some
   Borel `Phi : X_- -> X` intertwines `s~` with `L` and satisfies `pr_-(Phi(x)) T_- x` a.e. No lift is
   Laurent-realized. The same holds for any Borel p.m.p. `Q`-action on `X_-`, whether or not it lifts the symbol.

**Calibration (why Q is needed).**
* Theorem M fails for `SL_n(F_2[x])`. That group preserves `F_2[x]^n`, so the Haar measure of its annihilator, a
  copy of one half, is invariant and is neither `mu` nor atomic.
* For the polynomial half `B` whose Laurent matrices preserve `X_- x {0}`, the compression
  `q -> L_q|_(X_- x {0})` is a homomorphic lift into `Ê_-`. It is Laurent-realized with `Phi(x) = (x, 0)`. This is
  the half-lift mechanism of `jacobson-haar-relation-lifts-into-bilateral-relation` ("Halves").
* The proof uses two facts: `A^n` is finitely generated over the ring of the unipotent coefficients, and full-rank
  submodules are cofinite. Both fail for `F_2[x]`-submodules of `A^n`.

**Class killed.** Laurent-realized constructions of the splitting (HS) of
`jacobson-haar-relation-lifts-into-bilateral-relation`.
* *Members.* Any construction of a homomorphic lift `Q -> N_-` that produces the action on `X_-` by compressing
  Laurent matrices along an equivariant choice of positive half. This includes a Borel equivariant `psi`, a
  countably-valued `psi`, and any such choice corrected pointwise by `[T_-]`. It also includes extending the
  polynomial half-lifts in this way, and any gluing (for example (G2)) whose glued action stays Laurent-realized.
* *Named invariant.* The simplex of `Q`-invariant probabilities on the Laurent dual `X`, which is
  `conv(mu, periodic orbit measures)`.
* *Death step.* The push-forward of `mu_-` under the realizing map `Phi`. It is `Q`-invariant and atomless, because
  the fibres of `pr_- o Phi` are countable. So it is `mu`, and its image then has countable sections over `X_-`,
  which is `mu`-null by Fubini.
* *Survivors.* A lift `Q -> N_-` whose action on `X_-` is not tail-equivalent to the negative coordinate of any
  equivariant map into `X`. Such a lift is not Laurent-realized, and its failure to be so is forced by Theorem C.
  Point-dependent cocycles (ML), and placements `r ≠ pr_+` or `N > n` in `(BL_N)`, are untouched.

**Impact.**
* Every known lift over a large subgroup of `Q` comes from one of two sources. The polynomial halves are
  Laurent-realized. The finite, virtually free and amenable subgroups use abstract constructions: partitions,
  Bass–Serre gluing and cocycle vanishing. Theorem C rules out the first mechanism
  over `Q`. So any proof of (HS) must be abstract (non-Laurent) in the Kazhdan part, as the amenable lifts are. And
  any refutation of (HS) cannot use Theorem C alone, because it does not see non-realized lifts.
* Theorem M is the first complete measure classification on the survivor side of the Jacobson branch. The only
  non-Haar invariant measures of the bilateral Laurent action are the finite periodic models, which are exactly the
  models that make the bilateral relation sofic.
