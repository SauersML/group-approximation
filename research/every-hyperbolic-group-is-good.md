---
rg: 2
id: every-hyperbolic-group-is-good
kind: claim
title: Every word-hyperbolic group is good in Serre's sense
distinct_from:
  hyperbolic-finite-residual-is-torsion-free: that is the universal torsion-free-residual assertion, equivalent to universal residual finiteness; this is a profinite-cohomological assertion that implies it, with no converse known
  good-groups-have-no-persistent-finite-cohomology: that is a proved consequence of goodness for one group; this is the open assertion that every hyperbolic group is good
---

For every word-hyperbolic group `G`, every finite `G`-module `A` and every `q >= 0`, the
inflation map `H^q(G_hat;A) -> H^q(G;A)` is an isomorphism.

**Status: open.** By `good-cocompact-proper-groups-are-virtually-torsion-free` (H), this
implies that every hyperbolic group is virtually torsion-free and residually finite.
So it is at least as hard as Gromov's question. We did not check whether it is posed
as a named problem in the literature.

## Attempts

- **Through special cube complexes.** Hyperbolic virtually special groups are good
  (Kropholler–Wilkes, Theorem 9, recorded on
  `good-groups-have-no-persistent-finite-cohomology`). This covers exactly the
  cubulated hyperbolic groups, which are already residually finite. It dies at
  hyperbolic Kazhdan groups, which admit no proper cocompact cubulation, for example
  the density random groups above `1/3` (`gromov-density-random-groups-kazhdan-above-third`).
  No goodness theorem is known for them.
- **Only a weak form is needed downstream.** The route into
  `hyperbolic-finite-residual-is-torsion-free` uses only (G'). That is surjectivity of
  inflation with trivial `F_p` coefficients in large degrees, or even just onto the
  Chern–Quillen classes. The full isomorphism is never used.
- **The negative direction gives nothing by itself.** A residually finite hyperbolic
  group that is not good does not contradict residual finiteness. Non-goodness of a
  hyperbolic group decides neither root. What a counterexample to Gromov's question
  must fail is the specific surjectivity onto Chern–Quillen classes.
- **Entropy-measure transplant (swarm-0917-w9).** The idea was to replace finite quotients by a measurable
  object, lifts of p.m.p. actions across finite extensions, and to construct those lifts by ergodic methods.
  - `kazhdan-degree-two-goodness-iff-profinite-measurable-lifts` (ESTABLISHED, via Ioana's profinite cocycle
    superrigidity) shows the dictionary is exact in degree two for residually finite Kazhdan groups.
    - A lift of any free ergodic profinite action across a finite extension already forces virtual splitting.
    - Degree-two surjectivity of inflation for every finite-index `N` and finite `A` is equivalent to
      measurable lifts of `N ~> N̂`.
  - So in degree two the transplant gains nothing, exactly on the hyperbolic Kazhdan groups where the cubical
    route dies. Every measurable lift over a profinite action is a finite-quotient construction in disguise.
  - Lifts over Bernoulli-type or treeable actions do not help either. They carry no information about goodness:
    they force actual splitting (`central-bernoulli-lifts-force-splitting`) or always exist
    (`treeable-free-actions-lift-across-finite-normal-extensions`).
  - It dies at degree `>= 3`. Ioana's theorem controls 1-cocycles into groups, which reach degree two through
    extensions. No rigidity is known for measurable `q`-cochains with `q >= 3`. So the high-degree half used by
    `torsion-free-hyperbolic-mod-p-classes-die-virtually` has no measurable reformulation.
- **Group-ring / approximation transplant (swarm-0917-w11). Dead, killed by a calibrator.** The idea was to
  derive goodness, or just degree-two goodness, from inputs that make sense for any group and are known or
  expected for hyperbolic groups:
  - Strong Atiyah, domain group rings, and `L^2` vanishing with Lück approximation;
  - residual finiteness and residual-`p`, linearity, and finite type;
  - and, for the Kazhdan case where cubulation dies, property (T).

  **Calibrator.** `Γ(3) ≤ SL_3(Z)` has every one of these properties. It is torsion-free, Kazhdan, linear over
  `Z`, residually 3, and satisfies Strong Atiyah (`congruence-kazhdan-groups-satisfy-strong-atiyah`). Its group
  ring is a domain in characteristic 0 and 3. Yet it fails degree-two goodness
  (`sl3z-level-three-fails-degree-two-goodness`).
  - `b_2(Γ(3)) = 26` (`sl3z-level-three-congruence-subgroup-has-b2-26`, from Lee--Szczarba's `b_3 = 27` and
    Harder's `χ = 0`). So `|H^2(Γ(3); Z/n)| >= n^26`.
  - The profinite side is bounded independently of `n` (`sl3z-finite-index-fd-projective-multiplier-is-finite`).

  **Where every member of the class dies.** At the degree-two step. The invariant is the count
  `|H^2_cts(G^; Q/Z)[n]| >= n^(b_2) / |G^ab|`, which degree-two goodness forces for a Kazhdan group.
  - No combination of the listed inputs forces the profinite multiplier to be infinite: `Γ(3)` has all of them
    and a finite one.
  - So any proof of (G2) for hyperbolic Kazhdan groups must use hyperbolicity itself. Two candidate ingredients
    are closure of hyperbolicity under finite central extensions, and quasi-isometric rigidity of the
    extension.
  - **First concrete test.** The hyperbolic Kazhdan group of
    `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2` has `b_2 > 0`. If it is good in degree two, its
    profinite multiplier has `n`-torsion of order `>= n^(b_2) / |G^ab|` for every `n`. This is the opposite of
    `Γ(3)`.
  - **The `Z`-extension version.** `Γ(3)` also has a torsion-free finitely presented Kazhdan non-RF central
    `Z`-extension. This is the phenomenon a hyperbolic counterexample would need, realized here in higher rank.
