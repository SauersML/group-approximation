---
rg: 2
id: bounded-defect-free-full-contracting-rsgs-are-f-infinity
kind: claim
title: A full contracting RSG in which every element is a canonical similarity near all but finitely many points, and whose singular germs have zero defect in the groupoid homology of the SFT, is of type F_infinity with F_infinity finite-set stabilizers, so its twisted Brin-Thompson envelope is an F_infinity simple group; the defect obstructs BHM localization and is carried only by nucleus germs that are non-surjective or change the H_0 class (attribution: Belk-Hyde-Matucci Remark 2.13)
distinct_from:
  twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family: that reduces F_n of SV_L to F_n of the RSG family; this proves F_infinity of the family for the bounded, defect-free subclass.
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the Röver–Nekrashevych question (all RN groups have surjective nucleus, so zero defect); this covers the bounded RSG analogue and isolates what non-surjective nuclei add.
  finite-germ-extensions-with-singular-blocks-are-f-n: that generalizes BHM to singular blocks and shows blocks do not exist in full groups; this stays with singular points and adds the defect condition that BHM's localization axiom needs.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family
  - contracting-rsgs-have-fp-full-closures
```

**Status.**
- **Theorem 1: ATTRIBUTION to Belk–Hyde–Matucci, Remark 2.13** (arXiv:2407.03149: "any full, bounded, contracting
  RSG has type F_∞").
  - Added here: the zero-defect hypothesis that the indicated proof needs, and a checked proof (lane,
    bh-finf-hyp, 2026-09-19).
  - Referee bh-ref-q12: PASS with repairs for `F_∞` of `L`. The stabilizer and `SV_L` clauses are conditional on
    the unreviewed `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family`.
  - Nonzero defect does occur: see the Example below.
- **Source.** BHM was read in the arXiv PDF by the referee; the local TeX copy was lost in the 09-19 reboot.
- **Proposition 2 (defect): ESTABLISHED**, elementary.
- **Section 3: analysis and a route.**
- Inputs:
  - BHM, Corollary 2.10 (`cor:MainFinitenessCorollary`);
  - Matui: topological full groups of irreducible one-sided SFTs are `F_∞` (J. reine angew. Math. 705, 2015;
    recalled, not re-read);
  - BBMZ `prop:CyclicStabilizers` (germ groups of RSGs at rational points are virtually cyclic).

## Setting

- `Σ` is an SFT with irreducible core, `E` is clopen, and `L ≤ R_(Σ,E)` is a full contracting RSG. So
  `B := V_(Σ,E) ≤ L`.
- The irreducible core of `Σ` is not a single cycle, so `G_Σ|_E` is minimal and purely infinite (needed for
  Matui's bisections).
- A point `p` is **singular** for `g ∈ L` if `g` is not a canonical similarity on any cone around `p`, i.e. `g`
  agrees with no element of `B` near `p`.
- `L` is **bounded** if every element has finitely many singular points.
- **Defect.** For `p ∈ sing(g)` and a small clopen neighbourhood `U` of `p`, set
  `d_g(p) = [g(U)] − [U] ∈ H_0(G_Σ|_E) = coker(I − A^T)`.

## Theorem 1

Let `L` be bounded, with `d_g(p) = 0` for all `g` and all `p ∈ sing(g)`. Then:
- `L` is of type `F_∞`;
- so is `Stab_L(M)`, for every finite set `M` of rational points;
- `SV_L` (Belk–Zaremsky, over a rational orbit) is an `F_∞` simple group containing `L` undistortedly.

## Proposition 2 (the defect)

1. **Well defined.** `d_g(p)` does not depend on `U`. It is a germ invariant: `d_{g'}(p) = d_g(p)` whenever
   `g'` agrees with `g` near `p`.
2. **Additive.** `Σ_{p ∈ sing(g)} d_g(p) = 0` for every `g ∈ L`.
3. **Localization needs zero defect.** Let `h ∈ L` have `sing(h) = {p}`. Then `d_h(p) = 0`. So BHM's axiom (3),
   single-point localization, can hold at `p` only if `d_g(p) = 0`.
4. **Surjective nucleus gives zero defect.** Suppose every nucleus element `C_v → C_w` is onto, with
   `[C_v] = [C_w]` in `H_0(G_Σ)` (for example `v = w`). Then every defect vanishes. This includes all
   Röver–Nekrashevych groups, whose full shift has a single cone class.

## Proofs

**Proposition 2.**
1. **Independence of `U`.** Shrink `U` to `U' ⊆ U`. Then `U ∖ U'` avoids `sing(g)` near `p`, so it is a finite
   union of cones that `g` maps by canonical similarities. Canonical similarities preserve `H_0` classes, since
   cones of one type have one class. So `[g(U∖U')] = [U∖U']`.
2. **Additivity.** Cover `E` by disjoint small neighbourhoods `U_p` of the singular points and finitely many
   cones on which `g` is canonical. Then `0 = [gE] − [E] = Σ_p d_g(p)`.
3. **Localization.** Apply item 2 to `h`.
4. **Surjective nucleus.** For a small cone `U = C_α` around `p`, the local action `g|_α` is a nucleus element.
   So `g(U) = C_(ḡ(α))`, and `[g(U)] = [C_(t(ḡα))] = [C_(t(α))] = [U]`, using the hypothesis and the fact that
   a cone's class depends only on its terminal node.

**Theorem 1.** Check the hypotheses of BHM Corollary `cor:MainFinitenessCorollary` for `B ≤ L`.
- **`L` is a finite germ extension of `B`.**
  - (i) Every element has finitely many singular points (boundedness).
  - (ii) `B` is the set of elements with no singular points, since `B` is full.
  - (iii) Localization. Let `p ∈ sing(g)`, and choose a cone `U ∋ p` that meets no other singular point of `g`
    and with `U, g(U) ≠ E`.
    - `d_g(p) = 0` gives `[E ∖ U] = [E ∖ g(U)]` in `H_0(G_Σ|_E)`. Both sets are nonempty clopens.
    - `G_Σ|_E` is minimal and purely infinite, after pushing `E` into the irreducible core (BBMZ
      `prop:push_into_core`). So there is a compact open bisection `k` with source `E ∖ U` and range `E ∖ g(U)`
      (Matui). It is a finite union of canonical similarities between cones.
    - Put `h = g` on `U` and `h = k` on `E ∖ U`. Then `h` is a homeomorphism in `L` (fullness), `h` agrees with
      `g` near `p`, and `sing(h) = {p}`. This also covers `g(p) = p`.
- **Singular points are rational.**
  - Along a singular ray, the local actions of `g` form an infinite path of non-identity states in the finite
    nucleus automaton.
  - Boundedness makes these paths finite in number. So each is eventually periodic (König's lemma, plus two
    distinct cycles through one state giving uncountably many paths), and the ray is rational.
  - So `sing(L)` is a union of finitely many `B`-orbits of rational points: finitely many cycles, and `B`-orbits
    of rational points are determined by their tails.
- **(1) Oligomorphy.**
  - Mapping cones (BBMZ `cor:MappingConesWithV`) move any `n` distinct points of one tail class to any other `n`,
    through disjoint cone neighbourhoods.
  - So `B` acts on `sing(L)^n` with finitely many orbits.
- **(2) Stabilizers.** `Fix_B(M)`, for finite `M`, has a finite-index subgroup that is an iterated ascending HNN
  extension of some `V_(Σ,U)`.
  - This is item 1 of `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family`, applied to the full
    contracting RSG `B`, whose nucleus is the identity cones.
  - `V_(Σ,U)` is the topological full group of the reduction of `G_Σ` to `U`, which is `F_∞` (Matui).
  - Ascending HNN extensions preserve `F_∞`.
- **(3) Germs.**
  - `(L)_p` is virtually cyclic (BBMZ `prop:CyclicStabilizers`).
  - `(B)_p` is infinite cyclic at a rational point, generated by the germ of the tail shift, which exists in `B`
    by mapping cones.
  - So `|(L)_p : (B)_p| < ∞`.
- **Conclusion.** BHM gives `F_∞` for `L`.
  - The members of the family `𝓕(L)` of the twisted-BT node are full RSGs on clopens with nucleus inside
    `Nuc_L`. Boundedness and zero defect are properties of nucleus germs, so they hold for each member, and each
    member is `F_∞` by the same argument.
  - Item 1 of that node then gives `F_∞` for the finite-set stabilizers, and item 2 gives it for `SV_L`. These two
    clauses are conditional on that node, which is a lane proof not independently reviewed. ∎

**Example (referee bh-ref-q12): nonzero defect occurs.**
- **The space.** The full 3-shift, with `B = V_(3,1)` and `H_0 = Z/2`.
- **The half-shift** `n: E → C_0 ⊔ C_1`, given by `n(0x) = 0n(x)`, `n(1x) = 02x`, `n(2x) = 1x`. Its square is
  `x ↦ 0x`.
- **The element** `g`, defined by `g(0x) = 0n(x)`, `g(1y) = 1n^{-1}(y)`, `g(12x) = 02x`, `g(2x) = 2x`.
  - It is a homeomorphism, singular exactly at `0^∞` and `10^∞`, each with defect `1`.
  - So `L = [[⟨V_(3,1), g⟩]]` is bounded, full and contracting with nonzero defect.
- **Consequence.** Theorem 1 does not apply to it. Its `F_∞` is proved in
  `torsion-defect-costs-nothing-in-bhm-germ-complexes`.

## 3. Where Q1.2 stands for BBMZ hosts (analysis)

- **Surjective versus non-surjective.**
  - Röver–Nekrashevych: bounded implies `F_∞` (BHM theorem); polynomial activity, by induction (BHM remark);
    exponential activity is open. Their nuclei are surjective, so there is never a defect.
  - BBMZ hyperbolic hosts have **non-surjective** nucleus elements exactly at branch points
    (`pentagon-reflection-group-fails-cone-matching-at-wall-ends`). There, `g(U)` is a union of cones that is
    not a cone, and `d_g(p)` can be nonzero. That blocks single-point localization (Proposition 2.3).
- **Activity and dimension.**
  - In the right-angled pentagon group each generator fails cone matching along exactly 4 persistent chains at
    every tested level. That is consistent with boundedness, with finitely many singular points per generator.
  - For `∂Γ ≅ S^m` with `m ≥ 2`, the proposed mechanism (a reflection shears along the boundary of its wall)
    gives a whole wall-sphere of singular points, so exponential activity. This is not proved.
- **Route for nonzero defect (not proved).** Replace BHM's product of star trees by the subcomplex of
  **defect-balanced portraits**: finite sets of singular `B`-germs whose defects sum to zero.
  - Localization then holds for balanced pairs. Descending links become joins restricted by a sum condition in the
    finite abelian group `coker(I − A^T)`.
  - These are "zero-sum joins", which are highly connected for large support by a Hatcher–Vogtmann bad-simplex
    argument, as for the matching complexes of the horizontal node.
  - This would extend Theorem 1 to bounded RSGs with any defect. That is the natural next partial result for
    Fuchsian-type hosts.

## Lesson for general BH

- **Two independent measures of an RSG's distance from Röver–Nekrashevych.**
  - **Activity.** How many points an element is singular at. Bounded activity is handled by finite germ
    extensions.
  - **Surjectivity of the nucleus.** Germs that are non-surjective or change the `H_0` class carry a defect in
    `H_0` of the SFT, and localization must balance it.
- **For hyperbolic inputs.** Branching creates the non-surjectivity, and boundary dimension creates the
  activity. So for these inputs Q1.2 reads: **balanced germ complexes for bounded hosts** (1-dimensional
  boundaries), and **a new finiteness idea** for exponential activity (boundaries of dimension ≥ 2, including
  every Kazhdan case).

## Referee (bh-ref-q12, 2026-09-19): Theorem 1 PASS with repairs; Proposition 2 PASS with one repair; attribution to BHM Remark 2.13; nonzero defect occurs

**Source check.** Belk–Hyde–Matucci, arXiv:2407.03149, read in the arXiv PDF on 09-19. The local copy
`$GQ/src/bhm2407/main.tex` named in Status no longer exists after the 09-19 reboot.
- Condition (3) of a finite germ extension (their §1): "For every g∈G and p∈sing(g), there exists an h∈G with
  sing(h)={p} such that h agrees with g on some neighborhood of p."
- Remark 2.13: the class of Röver–Nekrashevych groups over bounded automata groups "generalizes in an obvious way
  to a class of bounded RSG's, and the proof of Theorem 2.12 generalizes to show that any full, bounded,
  contracting RSG has type F∞". "Bounded RSG" is not defined there.
- Their Proposition 2.11 verifies condition (3) using that `g_i` "maps the cone C_γ to some cone C_δ", and then
  swaps two cones by prefix replacement. That is exactly the step that needs zero defect: when the image of a
  small cone is not a cone of the same `H_0` class, no such swap exists (Proposition 2.3 here).

**Grading.**
- **Proposition 2.1–2.3: correct.** Well-definedness uses that the class of a cone `C_α` depends only on `t(α)`.
- **Proposition 2.4: correct.** One repair to the title and the Lesson: the defect is not carried *exactly* by
  non-surjective nucleus elements. It vanishes when every nucleus element maps its domain cone onto a cone of the
  same `H_0` class. A surjective nucleus element `C_v → C_w` with `[C_v] ≠ [C_w]` can also carry defect. Read
  "exactly" as "only at nucleus germs that are non-surjective or change the `H_0` class".
- **Theorem 1, `F_∞` of `L`: PASS.** Every hypothesis of BHM Theorem 1.1 / Corollary 2.10 was checked.
  - FGE (1) and (2): correct.
  - FGE (3), via a Matui bisection: correct. It needs `G_Σ|_E` minimal and purely infinite, i.e. the irreducible
    core is not a single cycle. **Repair:** add this to the Setting.
  - Rational singular points: correct. Every nucleus state is a local action of an element of `L`, so
    boundedness bounds the infinite non-identity paths from each state, and the König argument applies.
  - Oligomorphy: correct.
  - Stabilizers: correct. With `t ∈ Fix_B(p)` mapping `C_k` onto `C_(k+1)`, `Fix_B(p)` is the ascending HNN
    extension of `V_(Σ, E∖C_k)` by `t`. That group is `F_∞` by Matui (recalled).
  - Germ index: correct. BHM cite the same fact as [10, Prop. 5.5], i.e. BBMZ.
- **Theorem 1, `Stab_L(M)` and `SV_L`:** correct given `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family`,
  which is a lane proof not independently reviewed. Grade these two clauses as conditional on that node.
  "Undistortedly" is Belk–Zaremsky's embedding: recalled, not re-checked here.

**Nonzero defect occurs** (referee example, elementary). So the hypothesis of Theorem 1 is not vacuous.
- **Setting.** The full 3-shift `E = {0,1,2}^ℕ`, with `B = V_(3,1)`, `H_0 = Z/2`, and every cone of class 1.
- **The half-shift `n: E → C_0 ⊔ C_1`.** `n(0x) = 0n(x)`, `n(1x) = 02x`, `n(2x) = 1x`.
  - It is a homeomorphism onto `C_0 ⊔ C_1`, with local actions `{n, id}`.
  - `n²(x) = 0x`, a canonical similarity.
  - `n^(-1)(0x) = n(x)` for all `x`.
- **The element `g ∈ Homeo(E)`.** `g(0x) = 0n(x)`, `g(1y) = 1n^(-1)(y)` for `y ∈ C_0 ⊔ C_1`, `g(12x) = 02x`,
  `g(2x) = 2x`. The domain pieces `C_0, C_10 ⊔ C_11, C_12, C_2` go onto `C_00 ⊔ C_01, C_1, C_02, C_2`.
- **Singular points.** `sing(g) = {0^∞, 10^∞}`. The local action of `g` along both rays is `n`, and so is that of
  `g^(-1)`. So `d_g(0^∞) = d_g(10^∞) = [C_0 ⊔ C_1] − [E] = 1 ≠ 0`.
- **The group.** `L = [[⟨V_(3,1), g⟩]]` is a bounded full contracting RSG with nucleus `{id, n}`, since two `n`-germs
  compose to a canonical germ. Its singular set is the `V_(3,1)`-orbit of `0^∞`.
- **Consequence.** By Proposition 2.3, `L` is not a finite germ extension of `V_(3,1)`, so Theorem 1 does not apply
  to it. Its `F_∞` is the subject of `torsion-defect-costs-nothing-in-bhm-germ-complexes`; see the referee
  section there.

**Literature and credit.**
- **BHM Remark 2.13** asserts the `F_∞` conclusion for all full, bounded, contracting RSGs. Theorem 1 is that remark,
  with its indicated proof carried out under the hypothesis that makes the proof work.
  - Grade: **attribution to Belk–Hyde–Matucci**, with a precise hypothesis and a checked proof added here.
  - Nothing here shows the remark is false. The node correctly says only that the remark does not state the
    hypothesis.
- **Question 1.2.** No later paper found (searches 09-19) settles BBMZ Question 1.2 (arXiv:2309.06224) or
  Skipper–Zaremsky's `F_∞` question for `V_d(G)`. The results found:
  - BHM (bounded automata groups);
  - Belk–Matucci (Röver's group, arXiv:1312.2282);
  - Nekrashevych (finite presentation for contracting `G`);
  - Skipper–Witzel–Zaremsky;
  - Perego–Tarocchi, arXiv:2412.04138: `F_∞` for ESS groups from ∞-contractive replacement systems, including some
    groups on edge shifts. Their self-similar part acts by cell isomorphisms, so it does not obviously contain
    half-shift germs. This was not checked in detail.
- **The defect.** It is the germ-local form of Matui's `H_0` bookkeeping for SFT groupoids. I know no source that
  names it for RSG germs. No priority is claimed either way.

**Verdict: PASS with repairs:**
- the "exactly" wording;
- pure infiniteness in the Setting;
- the source path;
- the two clauses conditional on the twisted-BT node.
