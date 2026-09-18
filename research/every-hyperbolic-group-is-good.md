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
- **Operator-algebras transplant (swarm-0917-w10).** The idea was to replace
  finite quotients by operator-algebraic rigidity:
  - Kazhdan projections;
  - Popa spectral gap and `w`-rigidity;
  - finite-dimensional or twisted representations;
  - `L²` invariants.

  It dies at the step "conclude that the class restricts to zero on a
  finite-index subgroup". The obstruction is
  `titz-witzel-kernel-powers-have-noneffaceable-mod-p-classes`
  (ESTABLISHED). For the simple Titz Mite–Witzel kernel `K` and `m >= 1`:
  - `K^m` is torsion-free, of type `F`, CAT(0) and Kazhdan;
  - its profinite completion is trivial;
  - `H^(2m)(K^m;F_p) ≠ 0`.

  So every input shared by `K^m` fails in every even degree. In degree two,
  effacing a central class `x` is equivalent, by Malcev, to the twisted
  C*-algebra `C*(G, χ∘c)`, for a cocycle `c` of `x`, having a finite-dimensional representation. Rigidity
  that holds for `K` cannot produce one.

  There is also a degree-three heuristic, whose citation was not verified.
  - `H^3(G;T)` classes are the obstructions of `G`-kernels on the hyperfinite
    II_1 factor (Jones for finite groups; Sutherland). Effacement then reads as
    liftability after passing to a finite-index subgroup.
  - Nothing operator-algebraic is known to encode degree `>= 4`.

  What survives are inputs false on `K`: residual finiteness (the route's
  Lemma B), and hyperbolicity or its avatar, bi-exactness. `K^m` is not
  bi-exact for `m >= 2`. Whether `K` is bi-exact is the open test. The odd
  degrees, including degree 3 for the input
  `torsion-free-hyperbolic-mod-p-classes-die-virtually`, are untouched, because
  the odd cohomology of `K^m` vanishes.
