---
rg: 2
id: kazhdan-degree-two-goodness-iff-profinite-measurable-lifts
kind: claim
title: For a Kazhdan group, a finite extension virtually splits iff the profinite action lifts measurably across it, so degree-two goodness is a measurable statement
distinct_from:
  kazhdan-profinite-untwisting-is-virtual-splitting: that untwists scalar circle-valued multipliers by a Kazhdan projection and Peter--Weyl; this handles every finite (possibly non-central, non-abelian) kernel by Ioana's cocycle superrigidity and a finite-orbit argument, and wires the result to degree-two goodness
  central-bernoulli-lifts-force-splitting: that is the Bernoulli side, where a lift forces actual splitting; this is the profinite side, where a lift is equivalent to virtual splitting
  treeable-free-actions-lift-across-finite-normal-extensions: that shows lifts always exist over treeable actions; this shows that over profinite actions of Kazhdan groups a lift exists only when the extension already virtually splits
  ioana-profinite-cocycle-superrigidity: that is the imported cocycle theorem; this is its consequence for lifting the tautological cocycle across a finite kernel
  every-hyperbolic-group-is-good: that is the open universal goodness assertion; this proves that, for Kazhdan groups, its degree-two half is exactly a measurable-lifting statement over the profinite action, so ergodic methods gain nothing there
---

**ESTABLISHED** by `kazhdan-degree-two-goodness-profinite-lift-proof` (imports
`ioana-profinite-cocycle-superrigidity`, and `deligne-universal-cover-lattice-is-non-rf-kazhdan` for the
Deligne reading only).

**Setting.** `G` is a countable group with property (T). `G ~> X = lim G/G_n` is a free ergodic p.m.p.
profinite action (`G_n` a decreasing chain of finite-index subgroups). `1 -> A -> E -π-> G -> 1` is an extension
with `A` finite, not necessarily abelian or central. A **measurable lift** of the action across `E` is a measurable
cocycle `s : G × X -> E` with `π(s(g,x)) = g` for all `g` and a.e. `x`. Equivalently, `E` acts on `X × A`,
measure-preservingly, over the `G`-action, with `A` acting freely on the fibres. When `A` is abelian, a lift exists
iff the class of `E` dies in `H^2(G; L^0(X; A))`.

**Theorem.**
1. **Lift forces virtual splitting.** If the action lifts measurably across `E`, then `E` splits over a
   finite-index subgroup `G' <= G`: there is a homomorphism `σ : G' -> E` with `π σ = id`.
2. **Virtual splitting gives a continuous lift.** Suppose `E` splits over a finite-index `G'` by `σ`. Let `C` be
   the normal core of `σ(G')` in `E`, which is a finite-index normal subgroup meeting `A` trivially. Suppose also
   that the point stabilizers of some finite level `X_n` lie in `π(C)`. Then the action lifts across `E` by a
   cocycle that depends on `x` only through `r_n(x)`. On the profinite completion `X = Ĝ` of a residually finite
   `G` the hypothesis on `X_n` is automatic.

**Corollary (goodness in degree two).** Let `G` be residually finite with property (T), acting on `Ĝ`. The
following are equivalent:
- (a) for every finite-index `N <= G` and every finite `N`-module `A`, inflation `H^2(N̂; A) -> H^2(N; A)` is
  surjective (hence bijective);
- (b) for every finite-index `N <= G` and every extension of `N` by a finite abelian group, the action
  `N ~> N̂` lifts measurably across it.

The same holds for each fixed `N` and `A` separately. Item 1 needs only that `N ~> N̂` be free, ergodic and
profinite; `N` has (T) because it has finite index in `G`.

**Reading for the graph.**
- For `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`: `K_7` has (T).
  - Item 1 needs only a free ergodic profinite action. A measurable lift of *any* such action of `K_7` across a
    central `Z/n`-extension gives virtual splitting, hence inflation of that class (Step 3 of the route).
  - Conversely, item 2 turns (G2) into locally constant lifts over `K̂_7`, and item 2 does not use freeness.
  - When `K_7` is residually finite, which is not recorded, `K_7 ~> K̂_7` is free, and (G2) for `K_7` is exactly
    the existence of these lifts across every central `Z/n`-extension.
- For `every-hyperbolic-group-is-good` on residually finite hyperbolic Kazhdan groups (the groups where the cubical
  route dies), the degree-two half is exactly this measurable statement. So the entropy-measure dictionary is **exact** in degree
  two: every measurable construction of a lift over a profinite action is already a finite-quotient construction,
  and lifts over Bernoulli-type or treeable actions carry no information (they exist, or force actual splitting,
  independently of goodness; see `treeable-free-actions-lift-across-finite-normal-extensions`,
  `central-bernoulli-lifts-force-splitting`).
- Deligne's example becomes a measurable non-lifting theorem. Let `g >= 2`. For some `n >= 2`, the reduction mod
  `n` of the Deligne cover of `Sp_2g(Z)` lifts across no free ergodic profinite action of `Sp_2g(Z)`. The reason:
  if every reduction virtually split, the cover would be residually finite, which contradicts
  `deligne-universal-cover-lattice-is-non-rf-kazhdan` (Step 4 of the route).

**Where the transplant stops.** Ioana's theorem is about 1-cocycles into groups. It controls degree two through
extensions. Nothing like it is known for measurable `q`-cochains with `q >= 3`. The high-degree half of goodness
(`torsion-free-hyperbolic-mod-p-classes-die-virtually`) has no measurable reformulation from this argument.

**Model test** (calibration only, not part of the established statement).
- **Hypothesis side.** Property (T) is used once, through Ioana. Without it item 1 fails in the measurable sense.
  For amenable `G` the orbit relation is hyperfinite (Connes–Feldman–Weiss, standard, not re-read). So
  `H^q(G; L^0(X; A)) = 0` for `q >= 2` and every free action, by the Milnor `lim^1` sequence over finite
  subrelations. So every abelian-kernel extension of an amenable group
  lifts measurably, split or not. For free groups, lifts also always exist (treeable).
- **Conclusion side.** A virtually split extension lifts on every profinite action refining the splitting subgroup
  (item 2). So the dichotomy is sharp.
