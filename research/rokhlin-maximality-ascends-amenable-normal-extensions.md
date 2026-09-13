---
rg: 2
id: rokhlin-maximality-ascends-amenable-normal-extensions
kind: claim
title: If N is an amenable normal subgroup of W and W/N is Rokhlin-maximal, then W is Rokhlin-maximal
distinct_from:
  rokhlin-maximality-ascends-co-amenable-subgroups: that ascends from a co-amenable subgroup, where Følner sets of cosets are available; this ascends from a quotient by an amenable kernel, where the coset space W/N is the nonamenable quotient and no Følner sets exist.
  kun-thom-wreath-bernoulli-rokhlin-maximal: that is one explicit nonsofic amenable-by-residually-finite group; this is the permanence statement that would decide it and every group of the same shape.
---

**OPEN.** Let `N ◁ W` be amenable and suppose `W/N` is Rokhlin-maximal at `q`: the uniform Bernoulli shifts
over `W/N` have Rokhlin entropy `k log q` on `(A^k)^(W/N)`, where `|A| = q`. Then `W` is Rokhlin-maximal at `q`.

**Why it matters.**
- **The Kun–Thom wreath.** It decides `kun-thom-wreath-bernoulli-rokhlin-maximal` in the positive:
  `W = (Z/2) wr_(G/Γ) G` has locally finite lamps and a residually finite actor, which is sofic and hence
  Rokhlin-maximal (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`). That would be the first Rokhlin
  entropy lower bound over a nonsofic group.
- **The sofic analogue is false in this graph.** Soficity does not pass to amenable-by-sofic groups: `W` itself
  is nonsofic (`kun-thom-nonsofic-wreath`). So a proof cannot pass through finite models.
- **A counterexample.** A counterexample group would be nonsofic with an amenable kernel. It would refute
  `every-group-has-positive-rokhlin-entropy-action` through Seward's chain.

## Attempts

- **Co-amenable ascent with `H = N` (ex-rokhlin-lower, 2026-09-12).** Theorem A of
  `research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md` restricts to `H`, joins
  translates of a generating partition over a Følner set `Ω'` of `H\W`, and prices the recovered coordinates
  with the `H`-theory.
  - With `H = N`, the `N`-theory is Kolmogorov–Sinai entropy, which is available.
  - But `H\W = W/N` is the nonamenable quotient. Recovering coordinates in `N Ω''` needs translates over
    `Ω' ⊋ Ω''`, and `|Ω' \ Ω''|` is a fixed fraction of `|Ω'|`.
  - The boundary translates read coordinates outside `N Ω''`, which are independent of the interior. Their
    conditional entropy is not small, so no chain-rule refinement recovers the ratio.
  - It dies at the boundary count.
- **Actor-containing subgroups.** When `W = N ⋊ G`, inducing from `G` or from `M ⋊ G` fails when `G` has (T),
  because those subgroups are not co-amenable (`kun-thom-wreath-actor-subgroups-are-not-co-amenable`).
- **Quotient information.** Every factor on which `N` acts trivially has zero outer entropy
  (`infinite-subgroup-invariant-information-has-zero-outer-entropy`). So the lower bound cannot come from
  pulling back the maximal quotient's Bernoulli shift. The Bernoulli shift over `W` has no such factor anyway.
- **Finite models.** The localization theorems
  (`sofic-radical-localizes-bernoulli-deficit-witnesses`,
  `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers`) say that a counterexample witness folds on
  an invisible kernel element. Any proof must price the independent symbols at the two folded points without a
  model of the quotient's action on the kernel.
- **Finite kernels (ex-rokhlin-ascent-finite-kernel, 2026-09-13).** Split off as the open claim
  `rokhlin-maximality-ascends-finite-normal-extensions`, which this claim implies.
  - **No counting problem along the kernel.** For free ergodic `X`,
    `n h^Rok_W(X) <= h^Rok_(W/N)(X/N) <= n h^Rok_W(X) + r log n`
    (`rokhlin-entropy-quotient-formula-for-finite-normal-subgroups`). The `N`-quotient carries all the entropy, the
    opposite of the infinite-kernel bullet above. As a corollary, maximality descends along finite kernels
    (`rokhlin-maximality-descends-along-finite-normal-quotients`).
  - **Ascent for a pair is a statement about `W/N`.** It holds exactly when the twisted section action `Ω/N`, joined
    with Bernoulli shifts over `W/N`, has unbounded Rokhlin entropy
    (`rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded`). It follows when some liftable action is weakly
    contained in all free actions (`finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`).
  - **Where it stops.** At the extension class on Bernoulli orbit relations of `W/N`, not at Følner counting.
  - **Inclusion.** By Kaloujnine–Krasner, the finite case lies inside the split, locally finite case of this claim.
  - **Literature.** Not found in the six Seward and Alpeev–Seward papers searched (artifact
    `rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md`, Section 6).
- **Coherent kernel windows (ex-rokhlin-ascent-joint-counting, 2026-09-13).** Theorem A run with the roles
  reversed: Følner windows along `N`, maximality along `W/N`.
  - To stay compatible with `W`, the windows must satisfy `T_(wy) = w T_y w^-1`. That covers Ornstein–Weiss
    quasi-tilings of `N`-orbits in an auxiliary system, windows chosen as a factor, and coset windows for a
    complement.
  - Averaging such windows gives a mean on `N` invariant under translation and conjugation
    (`coherent-kernel-folner-windows-force-conjugation-invariant-mean`). For split extensions this is
    co-amenability of the complement, where Theorem A already applies. On the Kun–Thom wreath it fails.
  - Dead route: `amenable-kernel-ascent-via-coherent-kernel-windows`. Window counts are left with non-split
    extensions satisfying the mean condition, such as finite and central kernels.
- **What a proof needs.** An entropy count that averages along `N` (Følner sets exist) and along `W/N`
  (maximality holds) jointly, without a joint finite model. No such mechanism is known in the sources read
  (arXiv:1501.03367, 1602.06680, 1705.09707, 1804.05270, 1805.08279).
