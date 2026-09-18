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
- **Symbolic-dynamics transplant (swarm-0917-w12).** The idea was to replace finite quotients by compact
  `G`-spaces on which a class dies, and to find finite orbits by symbolic dynamics.
  - `primitive-shifts-detect-virtual-vanishing` (ESTABLISHED, elementary) shows the dictionary is exact in
    every degree. Each class `x ∈ H^q(G;A)` has a primitive shift `Σ(z) = {ψ : ψ∘∂_q = z}`.
    - `Σ(z)` is an affine SFT with an invariant Haar measure.
    - It is the terminal effacer: `x` dies over `X` exactly when there is a `G`-map `X -> Σ(z)`.
    - `Σ(z)^H ≠ ∅` exactly when `res_H x = 0`.
  - So goodness is exactly the statement "every primitive shift has a finite orbit".
  - **Where it dies.** It dies at the step from an effacer to a finite-index subgroup. That step is the
    existence of a periodic point in `Σ(z)`, which is `res_H x = 0` itself.
    - SFT, invariant measure, minimality, freeness (Gao–Jackson–Seward products) and expansiveness all come
      free for effacers, so none of them carries information.
    - Profinite odometers efface only effaceable classes.
  - **The principles are the wrong strength.** The principles that would supply periodic points fail.
    - On `Γ(3) <= SL_3(Z)`, the persistent classes of `sl3z-level-three-fails-degree-two-goodness` give a
      measured affine SFT with no finite orbit. They also give a linear SFT, on a torsion-free Kazhdan group
      of type F, whose periodic points are not dense.
    - `linear-coset-shift-periodic-density-iff-separable` (ESTABLISHED) shows that periodic density for
      linear SFTs forces LERF. So it fails on the good, non-LERF, Rips-construction hyperbolic groups, and it
      is strictly stronger than goodness.
  - **What survives.** "Primitive shifts of degree `>= 3` on torsion-free hyperbolic groups have finite
    orbits". This is equivalent to `torsion-free-hyperbolic-mod-p-classes-die-virtually`, not a reduction
    of it.
  - Artifact: `research/artifacts/primitive-shift-goodness-dictionary-2026-09-18.md`.

- **Goal relevance (2026-09-17, swarm-0917-w13-titz-pull, reframing). This node is inert for
  `torsion-free-sofic-exact-mf-radical-over-z`.** Neither a proof nor a disproof here can move the goal
  through the Titz--Witzel region. So the dispatcher's bounty on this node, which comes from that cone, is
  illusory.
  - *Result.* `fully-ramified-covers-cannot-create-titz-witzel-soficity` (ESTABLISHED) shows the following.
    Let `X' -> X_0` be any fully ramified tower over `Y_1^2`, for instance `Lambda \ D` for a torsion-free
    or normal finite-index `Lambda` in a complex of groups over `X_0`, and let it satisfy the flat-hitting
    condition (H). Then `beta(X') >= beta(X_0) + (1 - phi(X_0)) / [G : K]`. So sparse flat-hitting output
    forces the base to satisfy item 3 of `sparse-fully-branched-covers-iff-sofic-with-connected-links`,
    which is already equivalent to `titz-witzel-kernel-sofic`.
  - *Invariant.* The branched-sheet fraction `phi(X_0)` of the base.
  - *Step where every member dies.* Hitting an unbranched base component costs a whole fibre.
  - *Consequence.* Goodness, (V2), residual finiteness and cubulation of hyperbolic groups enter the cone
    only at the torsion-free or normal finite-index step, so they can never be the source of soficity of
    `K`. The flat-hitting node needs a partially ramified construction, and goodness is irrelevant to that.
  - Separately, `sp21-finite-congruence-kernel-forbids-p-goodness` already records CSP => non-good. There
    is no cheap route to a negative answer through arithmetic lattices of hyperbolic type, since uniform
    lattices in `Sp(n,1)` are hyperbolic and CSP for them is itself open.
