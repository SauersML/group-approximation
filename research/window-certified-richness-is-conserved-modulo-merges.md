---
rg: 2
id: window-certified-richness-is-conserved-modulo-merges
kind: claim
title: A left-preserving 2-to-1 wrapper whose constraints are certified by source windows that use every left label splits each window relation into forced 2-blocks and partial bijections, so its value is floored by a derived unique game up to the forced mass, the forced mass is capped by the entropy of the source's forced pairings, and over coset sources on any finite group the rich mass is a merge; windows that omit left labels, dummy padding among them, are outside the class
invalidates:
  - rich-2to1-via-window-certified-enrichment
distinct_from:
  left-preserving-local-richness-wrappers-are-affine-ug-merges: that needs an F_2-affine intended class and says nothing about non-affine classes (its gap G3, where a mixed type was not ruled out); this proves the component lemma and the value floor for an arbitrary intended class, shows mixed relations do occur but always split into forced 2-blocks plus partial bijections, extends the translation-or-merge dichotomy to cosets over every finite group with central involutions in place of F_2 translations, and sharpens the translation mass bound from alpha_k to c/((2k-1)(2k-3)).
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that kills constructions at perfect completeness through tractable skeleton search; this works at completeness 1 - beta and turns the wrapper into a unique-game hardness reduction with explicit loss, and adds the forced-pairing entropy count that applies to non-tractable windows.
  edge-conjugation-of-2to1-constraints-is-pure-gauge: that is one relabeling identity for one test; this classifies every window-certified right vertex and bounds the whole output value.
  unique-constraints-orient-at-most-half-of-a-fiber: that says bijections cannot implement a 2-to-1 merge; here the forced 2-blocks are exactly the part of a window relation that bijections cannot express, and the claim bounds how much edge mass that part can carry.
  separated-small-pairing-families-defeat-the-noise-test: that is about the noise test run on a small pairing family; this is about wrappers that keep the left labels and never run the test, and its entropy count is over the forced partial pairings that source windows derive.
  sd-rich-and-unique-games-sos-gaps-interconvert: that proves the BKM right merge turns unique games into rich 2-to-1 games; this shows the merge part of every window-certified wrapper is such a merge of an explicit derived unique game, and that the rest is bounded by forced source structure.
  derived-unique-game-lower-bounds-the-noise-test: that lower-bounds the long-code noise test, which re-encodes labels; this covers wrappers that keep the labels and is silent on re-encoding.
artifacts:
  - experiments/rich-2to1-window-components-2026-09-17/check_window_components.py
  - experiments/rich-2to1-kill-scope-audit-2026-09-17/check_full_hypothesis_is_loadbearing.py
---

**ESTABLISHED.** Fix `k >= 2`.

## Setting

*Source.* `G` is any finite constraint satisfaction instance. It has variables,
each with a finite alphabet, and constraints, each a relation on a tuple of
variables. A distinguished set `U` of variables has alphabets `Sigma_u` with
`|Sigma_u| = 2k`.

*Window-certified wrapper.* A wrapper `W` maps `G` to a weighted 2-to-1 game
`W(G)` that keeps the left labels:

* The left vertices are `U` with alphabets `Sigma_u`.
* Each right vertex `z` has a weight `w_z` (total 1), a neighbour set
  `S_z` in `U`, a neighbour law `nu_z` on `S_z`, and 2-to-1 maps
  `h_(uz) : Sigma_u -> [k]` (every fibre has size 2).
* Each `z` has a **window** `B_z`: a finite set of constraints of `G` whose
  variables include `S_z`, plus hidden variables. `Sol(B_z)` is its set of
  satisfying assignments. The **intended class** `A_z` is the projection of
  `Sol(B_z)` to `S_z`.

The wrapper may be deterministic or randomized, and may choose `S_z`, `nu_z`,
`w_z` and `h` any way it likes. Only these hypotheses are used:

* **(SLC) Source-local certification.** For every `f in A_z`, the value
  `h_(uz)(f_u)` is the same for all `u in S_z`.
* **(Full)** For every `u in S_z`, the projection of `A_z` to `u` is all of
  `Sigma_u`.
* **Completeness is certified.** A YES labelling `L` of `G` violates the windows
  of right-vertex mass at most `beta`. If `L` satisfies `B_z`, then
  `L|S_z in A_z`, so by (SLC) all constraints at `z` hold with right label
  `h_(uz)(L_u)`.

Everything below uses only the set `A_z`, a subset of `prod_(u in S_z) Sigma_u`.
So the theorem also covers abstract intended classes, for example the affine
ones of `left-preserving-local-richness-wrappers-are-affine-ug-merges`.

*Left marginal and richness.* Let `mu(u) = sum_z w_z nu_z(u)`. At `u`, draw `z`
with probability `w_z nu_z(u) / mu(u)` and let `P_(uz)` be the pairing of
`Sigma_u` into the fibres of `h_(uz)`.

* **(R2)** Any fixed pair is a block with probability `1/(2k-1)`, and any two
  disjoint pairs are both blocks with probability `1/((2k-1)(2k-3))`.
* **Full richness** means `P_(uz)` is uniform on all `(2k-1)!!` pairings.

## Theorem

**(1) Component lemma, for any source.** For `u != u'` in `S_z`, let `R_(uu')`
be the projection of `A_z` to `(u, u')`, viewed as a bipartite graph on
`Sigma_u` and `Sigma_u'`. Then:

* every connected component has at most 2 labels on each side, and `h` takes one
  value on it;
* for each value `c in [k]`, the components inside
  `h_(uz)^(-1)(c) x h_(u'z)^(-1)(c)` are either one `(2,2)` component or two
  `(1,1)` components.

So `R_(uu')` splits into:

* **forced 2-blocks**, the `u`-sides of the `(2,2)` components;
* a **partial bijection** `phi_(uu') : X_(uu') -> Sigma_u'`, where `X_(uu')` is
  the union of the `u`-sides of the `(1,1)` components, with
  `h_(u'z) o phi_(uu') = h_(uz)` on `X_(uu')`.

The forced pairing
`F_(uz) = { {a,b} : a != b, (a,a') and (b,a') in R_(uu') for some u', a' }`
is determined by the window alone. It is a partial pairing contained in the
block set of every 2-to-1 family that satisfies (SLC) over `A_z`. Mixed
relations, with some fibres forced and others bijective, do occur for general
sources (the artifact finds 8 among 60 feasible random windows).

**(2) Value floor and transfer.**

*Derived games.* Each game below draws `z ~ w` and then `u_0, u ~ nu_z`
independently. For `u_0 = u`, set `R_(uu)` to the diagonal, `X_(uu) = Sigma_u`
and `phi_(uu) = id`.

* `D_W` accepts iff `(L_(u_0), L_u) in R_(u_0 u)`.
* `U_W` accepts iff `L_(u_0) in X_(u_0 u)` and `L_u = phi_(u_0 u)(L_(u_0))`.
* `Ũ_W` is `U_W` with each partial bijection completed to a permutation
  `pi_(u_0 u)`. The two complements have equal size, twice the number of forced
  fibres.

*Forced edge mass.* `phi_W = Pr_(z ~ w, u_0 ~ nu_z)[ F_(u_0 z) != empty ]`.

For every left labelling `L`:

```text
val_W(L) >= val_(D_W)(L) >= val_(U_W)(L) >= val_(Ũ_W)(L) - phi_W,
```

and a labelling of `G` that violates window mass `beta` satisfies
`val_(Ũ_W)(L) >= 1 - beta - phi_W`.

Hence if `W o R'` proves `Gap-2-to-1(1 - beta, s)` hard from some problem with
certified completeness, then `x -> Ũ_W(R'(x))` proves
`Gap-UG(1 - beta - phi, s + phi)` hard from the same problem, where `phi`
bounds `phi_W` on all produced instances. Its alphabet is `2k`. The map runs in
polynomial time whenever the windows have polynomially enumerable solution sets,
for example constant-size windows.

**(3) Forced-mass entropy count.** For `j >= 1`, let `N_j(u)` be the number of
distinct nonempty forced partial pairings with `j` blocks that occur at `u`,
over all right vertices. Then:

```text
full richness:  phi_W <= sum_u mu(u) sum_(j>=1) N_j(u) (2k-2j-1)!! / (2k-1)!!
(R2):           phi_W <= sum_u mu(u) [ N_1(u)/(2k-1) + N_(>=2)(u)/((2k-1)(2k-3)) ]
```

Here `(2k-1)!!/(2k-2j-1)!!` is about `(2k)^j`. Two consequences follow:

* **Whole-pairing forcing.** Suppose every nonempty forced structure is a whole
  pairing, taken from a family `P_u` of `N_k(u)` pairings. Under full richness,
  `phi_W <= max_u N_k(u)/(2k-1)!!`. So a family of size `2^(o(k log k))` gives
  `phi_W = o(1)`, and the wrapper collapses by (2) to a unique game.
* **Gate.** A window-certified wrapper can carry non-merge richness on edge mass
  `phi` only if the source windows derive, at a typical left vertex, about
  `phi (2k)^j` distinct forced partial pairings with `j` blocks, for some `j`.

**(4) Coset sources over any finite group.** Suppose every variable of `G` takes
values in a finite group (so `Sigma_u = H_u`), and every constraint is a left
coset of a subgroup of the product of its variables' groups. Examples are
`Gamma`-Max-2-Lin, affine systems, and affine intended classes.

*Purity.* `R_(uu') = (a_0, a_0') T` for a subgroup `T` whose projections onto
both factors are full. With `N = {x : (x,1) in T}`, every component is
`a_0 x N` times a coset of `N'`, and `|N'| = |N|`. So all components of one
relation have the same size:

* `|N| = 1`: a coset bijection `a -> a_0' theta(a_0^(-1) a)` for an isomorphism
  `theta`;
* `|N| = 2`: `N = {1, b}` with `b` a central involution, and the relation forces
  the whole translation pairing `P_b = { {y, yb} }`;
* `|N| > 2`: no 2-to-1 family satisfies (SLC).

*Dichotomy.* Every feasible right vertex is of exactly one type:

* **(T) Translation.** If any pair at `z` is forced, then every neighbour's
  pairing `P_(uz)` is `P_b` for a central involution `b` of `H_u`.
* **(D) Merge.** Otherwise every `R_(uu')` is a coset bijection. Then `z` is the
  BKM right merge of a coset unique-game clique.

*Mass bound.* Let `c = max_u c_u`, where `c_u` is the number of central
involutions of `H_u`. Under (R2),

```text
w(T) := Pr_(z ~ w, u ~ nu_z)[ z of type (T) ] <= c / ((2k-1)(2k-3)) <= 1/(2k-3).
```

Under full richness the bound is `c/(2k-1)!!`. If no `H_u` has a central
involution (for example `S_3`, or dihedral groups `D_(2m)` with `m` odd), the
bound is `0`.

*Floor.* `val_W(L) >= w(D) val_(U^D_W)(L)`, where `U^D_W` is the coset unique
game drawn from type-(D) vertices. So a certified coset wrapper proves at most
`Gap-UG(1 - beta/w(D), s/w(D))` hardness of `U^D_W(G)` from the same source.

## Where the class dies

* **Invariant.** The component skeleton of the window relations `R_(uu')`. Its
  bijective part is a unique game. Its forced part consists of 2-blocks that the
  source itself already derives.
* **Step.** A 2-to-1 map at `z` sees the source only through `A_z`. Whatever
  richness it adds on the bijective part is a right merge of `U_W`, and it pays
  for itself: `val_W >= val_(Ũ_W) - phi_W`. The rest lives on forced blocks, and
  (3) caps their mass by the number of distinct forced partial pairings.
* **Conservation law.** For window-certified wrappers, richness is conserved
  modulo merges. The wrapper's own randomness and design can only enrich the
  merge part, because `F_(uz)` depends on the window and not on `h`.
* **Covered.** Any transformation of a source instance that keeps its left
  labels and whose completeness proof is "a YES labelling satisfies the window".
  The transformation may be local, deterministic, randomized or low-entropy.
  This includes:
  * right compression, merging and auxiliary right vertices;
  * right vertices certified by bounded-size sub-instances;
  * affine and all finite-group coset refinements of proved instances.
  The identity wrapper is consistent with the theorem. Its windows are the stars
  of `G`, and its forced pairings are `G`'s own pairings, so it is exactly as
  rich as `G`.
* **Common invariant of the earlier dead attempts.** The dead attempts listed
  under the Rich 2-to-1 claim all run into the same quantity: the pairing entropy
  available at a left vertex. This is informal for them, since padding and the
  noise test change the alphabet.
  * Affine and separated-family noise tests fail on subexponential families.
  * Edge conjugation leaves the analytic object unchanged.
  * Unique gadgets cannot create 2-blocks.
  * Padding sits at the random-guessing floor.
  For label-keeping, window-certified wrappers *that satisfy (Full)*, (2) and
  (3) make this exact. Padding is **not** among them: its windows never mention
  the dummy labels, so (Full) fails and it sits in survivor (S4) below. Its
  random-guessing floor stays informal here. See the 2026-09-18 audit under
  `## Attempts`.

**Survivors.** Not covered:

* **(S1)** Non-coset windows whose forced partial-pairing families pass the
  gate in (3). Sparse forcing, with one or two blocks per window but `Omega(k)`
  distinct blocks, passes the count. So (3) is a necessary condition, not a
  kill of that subclass.
* **(S2)** Completeness proofs with no source-local certificate. The YES
  labelling satisfies the new constraints through global structure of the YES
  instance, not window by window.
* **(S3)** Label re-encoding, such as long codes or composition. Here `Sigma_u`
  is not a source alphabet.
* **(S4) Alphabet-restricting windows.** `A_z` does not project onto `Sigma_u`,
  so (Full) fails. Padding, core-plus-dummy alphabets and any wrapper whose
  window pins a variable to a proper subset live here. They can be fully rich
  with `phi_W = 0` and are not floored by the derived unique game: at the
  witness class `A_z = {(0,0),(1,1)}` the pointwise chain of (2) fails by
  `1 - 1/(k-1)`. Whether they can be *hard* is a separate question, on which
  this theorem is silent.

This neither proves nor refutes UGC or the Rich 2-to-1 Conjecture.

DERIVATION window-certified-richness-conservation-proof

## Attempts

* **2026-09-18, e2-w2-audit-ugc2 (calibration): adversarial scope audit of the
  class kill. Verdict: survives as a theorem, but the class it kills is smaller
  than the prose claimed, so the title is narrowed.** Three lenses were run:
  proof gaps, imports, calibration.

  * **Artifact re-run.** `check_window_components.py` reproduces every printed
    number of the claim exactly: 60 feasible full windows with 8 mixed pair
    relations; Part C tight at `1/3` on `Z_4` and `1/15` on `Z_6`;
    `1/105 <= 0.0286` on `D_4` and `Q_8`; `7/105 <= 0.2` on `Z_2^3`; `0` on
    `S_3`. Runtime 1.1 s, `ALL CHECKS PASS`.
  * **Proof lens: (1) to (4) hold as written.** Checked line by line. The
    component lemma, `val_W >= val_D` (via `sum_m p_m^2 <= max_m p_m`),
    `val_D >= val_U`, the completeness count, the disjointness of the events
    `F_(uz) = t`, the `(2k-2j-1)!!/(2k-1)!!` count, Goursat with `|N| = |N'|`,
    the central-involution case analysis, and the Markov step on
    `Q(P) = sum_b C(n_b, 2)` are all correct.
  * **Scope defect found: the hypothesis (Full) is load-bearing, and the
    "Covered" paragraph over-reaches.** "Covered" asserts *any* label-keeping
    transformation with a window-local completeness proof, and the paragraph on
    earlier dead attempts says (2) and (3) "make this exact" for **padding**.
    Dummy padding (`dummy-padding-cannot-beat-the-random-guessing-floor`: "a
    hard core of alphabet size `K` is hidden inside a much larger randomly
    matched dummy alphabet") is exactly a wrapper whose windows never mention
    the dummy labels, so its `A_z` does not project onto `Sigma_u` and (Full)
    fails. The theorem does not cover it.
  * **Where the proof dies without (Full).** In (2), the step "Suppose `Ũ`
    accepts but `U` rejects. Then `L_(u_0)` is outside `X_(u_0 u)`, so
    `R_(u_0 u)` has a `(2,2)` component, and so `F_(u_0 z)` is nonempty" is
    false: a label omitted by `A_z` is isolated or sits in a `(1,2)` component,
    which puts nothing in `F_(u_0 z)`. The artifact
    `check_full_hypothesis_is_loadbearing.py` enumerates every window on
    `Sigma = [4]` admitting an SLC-feasible 2-to-1 pair: all 834 (Full) windows
    keep the implication, and 532 of the 2644 non-(Full) ones break it.
  * **The entropy count (3) cannot be repaired to cover them.** The quantity the
    argument needs is `phi'_W = Pr[X_(u_0 u) != Sigma_(u_0)]`, not
    `phi_W = Pr[F_(u_0 z) != empty]`. At the witness window
    `A_z = {(0,0),(1,1)}` over `Sigma = [2k]` every forced partial pairing is
    empty, so `N_j(u) = 0` for all `j >= 1` and (3) returns `phi_W <= 0`, while
    `phi'_W = 1`. A window that *omits* labels pays no pairing entropy, so the
    gate in (3) prices nothing on this subclass.
  * **Quantitative counterexample to the pointwise chain of (2).** Source:
    variables `u_1, ..., u_d` with alphabet `[2k]`, one window per right vertex
    certifying "all `u_i` equal and in `{0,1}`". (SLC) holds, completeness is
    certified with `beta = 0`, `phi_W = 0`, and every left vertex is **fully
    rich**: (SLC) only fixes the names of the `0`- and `1`-fibres, so all
    `(2k-1)!!` pairings occur and the wrapper can make them uniform (verified by
    enumeration up to `k = 5`). At the dummy labelling `L = 2`:

    ```text
    k   d   val_W(L)   val_D(L) = val_U(L)   val_Ut(L) - phi_W
    2   8    0.7578          0.1250                1.0000
    3   8    0.5713          0.1250                1.0000
    4   8    0.4769          0.1250                1.0000
    ```

    with `lim_(d -> inf) val_W(L) = 1/(k-1)` for `k >= 3` (and `2/3` at
    `k = 2`). So `val_W >= val_Ũ - phi_W` fails by `1 - 1/(k-1) -> 1`, and
    `val_U >= val_Ũ - phi_W` fails by a factor `d`. The mechanism is that
    alphabet restriction **decouples** the neighbours: (SLC) over a proper
    subclass constrains only the fibres the window names, leaving each
    neighbour's remaining fibre naming free and independent.
  * **Calibration lens: no false kill.** The identity wrapper is (Full), forces
    every pairing, and (3) then needs `N_k(u)` of order `(2k-1)!!` -- exactly
    full richness, so the gate is calibrated. The BKM right merge of a unique
    game (`sd-rich-and-unique-games-sos-gaps-interconvert`) is the type-(D) case
    and is consistent. The proved 2-to-2 Grassmann reductions re-encode labels
    and sit in survivor (S3), so the theorem does not contradict them.
  * **Narrowing applied.** The title now says "windows that use every left
    label" and names the exclusion. Add to the Survivors list:
    * **(S4) Alphabet-restricting windows.** `A_z` does not project onto
      `Sigma_u`. Padding, core-plus-dummy alphabets and any wrapper whose
      window pins a variable to a proper subset live here. They can be fully
      rich with `phi_W = 0` and are not floored by the derived unique game.
      Whether they can be *hard* is a separate question -- the random-guessing
      floor of `dummy-padding-cannot-beat-the-random-guessing-floor` still
      applies informally -- but this theorem does not make that exact.
  * Everything else in the claim stands, at the stated hypotheses. Status kept
    **ESTABLISHED** for the narrowed statement.
