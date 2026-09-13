# Ideas: separating permutational Boone–Higman from Boone–Higman

Lane `bh-pbh-separation`, 2026-09-13. Target: `boone-higman-conjecture`.

Lens: does BH imply PBH? BFFHZ call this "a fundamental question", and FFWZ call it
"a major question whether (PBH)⇔(BH)" (both quoted in `permutational-boone-higman-conjecture`).

This is an idea file only. No node was edited, and nothing is established.

## Calibration

- **One direction is imported.** By BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`), every subgroup of a finitely presented simple MIF group lies in B_A. By Zaremsky Corollary B, every member of B_A embeds in a finitely presented simple twisted Brin–Thompson group. So BH ⇒ PBH is at least as strong as BFFHZ Question 3.4 restricted to hosts of decidable groups (`fp-simple-groups-embed-in-fp-simple-mif-groups`). I did not re-check that twisted Brin–Thompson hosts are MIF, so I only use the first direction.
- **The relative-to-absolute step is already reduced on main.** It follows from FFWZ Theorem C (`boone-higman-implies-relative-permutational-bh`) together with `a2-kernel-removable-iff-image-in-type-a2-actor`. It is not repeated here.

## 1. Affine type (A) actors: orbit-finite automorphism groups (survives as a reformulation)

**Idea.**
- Setup: let S be a group and W ≤ Aut(S) finitely generated. Let Γ = S ⋊ W act on S by (s, w)·x = s·w(x).
- Hand check:
  - the action is faithful and transitive, and the stabilizer of 1 is W;
  - (x, y) ↦ the W-orbit of x⁻¹y classifies Γ-orbits of ordered pairs. It is invariant, and if x′⁻¹y′ = w(x⁻¹y) then s = x′·w(x)⁻¹ sends (x, y) to (x′, y′).
- So the action is of type (A) exactly when Γ is finitely presented and W has finitely many orbits on S.
- S itself need not be finitely generated or finitely presented.
- **The Mikhailova case.** W = Inn(S) with Z(S) = 1 gives S × S ↷ S, whose pair orbits are the conjugacy classes. The affine form relaxes inner automorphisms to arbitrary orbit-finite automorphism groups.

**What it would prove.** Every G ≤ S ⋊ W lies in B_A. A universal version would give PBH, hence BH: every decidable G sits inside some finitely presented S ⋊ W with W orbit-finite on S, and G may sit inside W.

**Kill tests run.**
- **(a) An infinite finitely presented affine actor beyond Mikhailova exists, apparently.**
  - Take S = C(C, F₂), the locally constant F₂-valued functions on the Cantor set, and W = V.
  - V has three orbits on S: 0, 1, and the indicators of proper nonempty clopen sets (V is transitive on those).
  - S ⋊ V should be isomorphic to the centralizer in V of a fixed-point-free involution, via the two-sheet quotient. This is a hand sketch, not source-checked.
  - Martínez-Pérez–Matucci–Nucinkis (arXiv:1309.7858, abstract checked; hypotheses not checked) prove that centralisers of finite subgroups in such V-type groups are of type F∞.
  - So this looks like a genuine finitely presented affine type (A) actor. Unlike approach 2, the affine criterion does not presuppose Makowsky's FP19. As a source of inputs it is useless, since it embeds in V.
- **(b) Retract observation.** S ⋊ W retracts onto W, and retracts of finitely presented groups are finitely presented. So W must be finitely presented. For S = C(C, F₂) and W ⊇ V, the idea then falls under the known full-Cantor case (`fp-full-binary-cantor-groups-have-type-a-actions`) whenever W is full.
- **(c) Spreading an input over the Cantor set.** Take S = C(C, G), with W ⊇ V together with pointwise inner automorphisms. The finite set of conjugacy classes of G that occur is an invariant, so W has infinitely many orbits unless G is conjugacy-finite. The natural spreading constructions therefore return to FP19-type conditions (approach 2).

**Verdict: survives, as a design principle, not a construction.** Type (A) actors can be built from orbit-finite automorphism groups of "Boolean-like" normal subgroups. Universality is unclear. The input has to enter through W, not S, and W has to be finitely presented.

**Next test.** Find a finitely presented W containing a decidable, non-conjugacy-finite infinite group and acting with finitely many orbits on some countable group S, with S ⋊ W finitely presented, where W is NOT a full Cantor group, so that the known node doesn't already cover it.

## 2. Conjugacy-finite hosts and FP19 (killed as a working route)

**Idea.** Suppose G ≤ T with T finitely presented, Z(T) = 1 and finitely many conjugacy classes. Then T × T ↷ T is of type (A) (approach 1 with W = Inn T), so G ∈ B_A. So the repo's "shortest sufficient condition for Boone–Higman", `every-wp-group-embeds-in-fp-conjugacy-finite-group`, is already sufficient for PBH, not only BH. On the separation side, every BH host we know has infinitely many conjugacy classes.

**Kill test run.** Apply the hypothesis to G = Z. It produces an infinite finitely presented group with finitely many conjugacy classes, which is a positive answer to Makowsky's FP19: "Is there an infinite finitely presented group with finitely many conjugacy classes?" (Shpilrain's problem list, via search results). Osin's finitely generated infinite groups with two conjugacy classes are not finitely presented (search summary). So this sufficient condition is at least as hard as FP19. The node does not currently mention FP19 (grep on main).

**Verdict: killed as a route for either conjecture.** Record that `every-wp-group-embeds-in-fp-conjugacy-finite-group` implies a positive answer to FP19, and implies PBH.

## 3. Separation by word-problem complexity (killed as an independent separator)

**Idea.**
- Twisted Brin–Thompson hosts have word problem equal to an actor's orbit problem (`twisted-brin-thompson-wp-equals-actor-orbit-problem`).
- Type (A) point stabilizers have decidable membership (`finite-bi-index-subgroups-have-decidable-membership`).
- Look for a decidable G that embeds in some finitely presented simple group, but whose word problem is harder than the orbit problem of every type (A) actor.

**Kill test run.** `type-a-actors-with-arbitrarily-hard-word-problem` is OPEN. Its node says it implies `fp-simple-groups-with-arbitrarily-complex-word-problem` and is equivalent to the restriction of that root to finitely presented twisted Brin–Thompson groups. Clause (c) of `twisted-brin-thompson-wp-equals-actor-orbit-problem` transfers hardness between hosts and actors with linear length control. So a complexity gap between BH hosts and PBH hosts is exactly the statement that finitely presented simple groups beat every twisted Brin–Thompson group. That is the shared complexity root itself, not a mechanism.

**Verdict: killed**, since it collapses onto the shared complexity root.

## 4. Invariants that pass to subgroups (killed as a method)

**Idea.** Find a property of every finitely presented simple MIF group that passes to all subgroups but fails for some subgroup of some finitely presented simple group.

**Kill test run** on the obvious candidates:
- **Laws and mixed identities.** MIF constrains only the host. Subgroups such as Z satisfy mixed identities, so nothing passes down.
- **Torsion, amenability, property (T), FW.** V already contains every finite group and non-amenable subgroups, and nothing forbids Kazhdan subgroups. The established `finite-bi-index-kazhdan-subgroup-forces-nonamenability` only forces the actor to be nonamenable, which it is anyway.
- **Stabilizer finiteness of oligomorphic actions.** Fournier-Facio–Kropholler–Lyman–Zaremsky (arXiv:2506.02319, abstract checked) prove it only for groups of finite virtual cohomological dimension and countable linear groups. An infinite finitely presented simple host is not linear, because finitely generated linear groups are residually finite. A host containing torsion of all orders has no finite vcd. So it does not reach these hosts.
- **Word-problem degree.** See approach 3.

**Verdict: killed as a method.** A separation has to be embedding-level, about finitely presented simple MIF overgroups of one specific group, not a property inherited by subgroups.

## 5. Kazhdan twin-building lattices as test inputs (unclear)

**Idea.** Caprace–Rémy (arXiv:math/0607664; statement taken from a search summary, not read in the source): for a 2-spherical generalized Cartan matrix and q > 1764n, Λ/Z(Λ) is finitely presented, simple and Kazhdan. Take S = Λ/Z(Λ) as a candidate for BH \ PBH. Its natural actions are not of type (A), by a hand check:
- chambers: the Bruhat double cosets B\Λ/B correspond to the infinite Weyl group;
- spherical parabolics: the double cosets W_J\W/W_J are infinite for any spherical J in an infinite Coxeter group.

**What it would prove.**
- A proof that S embeds in no finitely presented type (A) actor would separate PBH from BH.
- An embedding would be a new positive case, putting these lattices in B_A.

**Kill test run.** No established obstruction on main is violated by Kazhdan subgroups of type (A) actors (see approach 4). Nor does any source I checked show a type (A) action or a MIF simple overgroup for S.

**Verdict: unclear.** It is a concrete test input, not a mechanism.

**Next test.** Does S have an infinite-index finitely generated subgroup with finitely many double cosets, i.e. a faithful action with finitely generated stabilizers and finitely many pair orbits? Candidate sets: twin apartments, or pairs of opposite chambers.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Affine type (A) actors | survives as a reformulation; the input must enter through a finitely presented W |
| 2 | Conjugacy-finite hosts | killed; the sufficient condition on main implies FP19 and already gives PBH |
| 3 | Complexity separation | killed; collapses onto the shared complexity root |
| 4 | Subgroup-hereditary invariants | killed as a method |
| 5 | Kazhdan twin-building lattices | unclear; a test input |

No priority or novelty is claimed.

## Sources checked

- arXiv:2506.02319, abstract.
- arXiv:1309.7858, abstract.
- Shpilrain, "Finitely presented groups" problem list (FP19), via search results.
- arXiv:math/0607664, via a search summary only.
