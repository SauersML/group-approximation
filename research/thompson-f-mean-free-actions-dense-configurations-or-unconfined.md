---
rg: 2
id: thompson-f-mean-free-actions-dense-configurations-or-unconfined
kind: claim
title: Thompson's F has a mean-free amenable action exactly when finite configurations in (0,1) carry an invariant mean meeting every interval, or an F-set with non-confined stabilizers carries a mean-free one; amenability of F gives both, and both give soficity
distinct_from:
  thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived: that makes following-model witnesses equivalent to a mean-free amenable action on some F-set; this splits every such action into a configuration part and a non-confined part, and kills every bounded configuration type.
  thompson-f-interval-stabilizer-cosets-separate-only-if-amenable: that collapses the particular non-confined cosets F/F_Z and amenable H to amenability; this disposes of all confined stabilizers at once and names the two surviving witness shapes.
  thompson-f-following-models-separate-iff-mean-charges-commutator: that proves null slabs for equivariant maps to [0,1]; this handles canonical finite fixed sets of unbounded size, where slab arguments give no contradiction.
artifacts:
  - research/artifacts/hl-f-mean-free-actions-2026-09-14.md
---

**ESTABLISHED.** The imports are pinned verbatim in `thompson-f-confined-subgroups-fix-finite-sets`
and `elek-szabo-essentially-free-amenable-actions`.

**Setting.**
- `F` acts on `[0,1]` as usual; `F'`, `c`, `Fix`, `Moved` and invariant means are as in
  `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`.
- A *mean-free amenable action* is an `F`-set with an invariant mean `m` and `m(Fix(g)) = 0` for all
  `g ≠ e`. This is Elek–Szabó's "essentially free amenable action".
- `Conf` is the `F`-set of finite subsets `S ⊂ (0,1)`, with `g·S = g(S)`. For an interval `I` put
  `n_I(S) = |S ∩ I|`.
- For an `F`-set `Ω`, `Ω_conf = {ω : Stab(ω) is confined in F}` and `Ω_free = Ω \ Ω_conf`; both are
  `F`-invariant. For `ω ∈ Ω_conf` put `S(ω) = {u ∈ (0,1) : h(u) = u for all h ∈ Stab(ω)}`.
- `supp(q)` is the closure in `[0,1]` of `{u : q(u) ≠ u}`.

**Statement.**
1. **Canonical configurations.** For `ω ∈ Ω_conf`:
   - `S(ω)` is finite, and `S(gω) = g·S(ω)`;
   - `ω ∈ Fix(q)` for every `q ∈ F'` with `supp(q) ⊆ (0,1) \ S(ω)`.
2. **Split.** `F` admits a mean-free amenable action if and only if at least one of the following holds.
   - **(I)** `Conf` carries an invariant mean `m` with `m({S : S ∩ J = ∅}) = 0` for every nonempty open
     interval `J ⊆ (0,1)`. Such a mean is mean-free.
   - **(II)** Some `F`-set in which no point stabilizer is confined carries a mean-free invariant mean.
3. **Bounded configuration types carry no separation.** For every invariant mean `m` on every `F`-set
   `Ω` and every `k ≥ 0`, `m(Moved(c) ∩ {ω ∈ Ω_conf : |S(ω)| ≤ k}) = 0`.
   - In particular `m(Moved(c)) = 0` on every transitive `F/H` with `H` confined.
   - This covers stabilizers of points of `(0,1)` and of the Cantor set, germ stabilizers, pointwise
     stabilizers of finite configurations, and every subgroup between `St⁰_(F')(S)` and `St_F(S)`.
4. **Profile of (I).** A mean as in (I) has `m(n_I / n_(I')) = 0` whenever `I, I'` are compact intervals
   with `I ⊆ int(I') ⊆ (0,1)`. The quotient is read as `0` when `n_(I') = 0`.
   - So mean-almost every configuration meets every interval.
   - Yet inside every interval, its points concentrate at the ends at every scale.
5. **Both shapes sit between amenability and soficity.** If `F` is amenable, (I) and (II) both hold.
   Each of (I) and (II) implies that `F` is sofic.
6. **Obstruction group.** The characteristic subgroup `N_F` of Elek–Szabó §5 is `1` or `F'`. So either
   (I) or (II) holds, or `m(Fix(g)) = 1` for all `g ∈ F'`, every invariant mean `m` and every `F`-set.

**Consequences.**
- **Barrier.** Refuting (I), (II), or following-model soficity of `F` in any form proves that `F` is not
  amenable (item 5). Proving (I) or (II) proves that `F` is sofic.
- **Natural actions** (directive of lane `hl-f-mean-free-actions`):
  - points, parabolic subgroups, breakpoint and Cantor-set point stabilizers, germs and finite
    configurations are all confined, so `t = m(Moved(c)) = 0` (item 3);
  - interval stabilizers `F_Z` with interior are not confined, and they collapse to amenability
    (`thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`);
  - the regular action needs amenability.
- **What remains.** Witnesses need configurations of unbounded size, or stabilizers whose conjugates
  converge to the trivial subgroup.

**Scope.** Elementary given the imports.
- Items 5 and 6 are close to folklore.
- Item 3 generalizes item 1 of `thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`.
- It leaves `thompson-f-is-sofic` and `thompson-f-is-amenable` OPEN.

Proof route: `thompson-f-mean-free-actions-configuration-split-proof`.
