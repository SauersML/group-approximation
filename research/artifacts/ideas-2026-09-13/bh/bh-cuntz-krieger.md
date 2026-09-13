# Ideas: Boone–Higman through full groups of Cuntz–Krieger, higher-rank-graph and product groupoids

Lane `bh-cuntz-krieger`, 2026-09-13. Target: `boone-higman-conjecture`.
This is an idea file. No Cairn node is edited, and nothing here is established.

## Constraints used as kill tests (nodes on main at d8e7335b7)

- `complexity-bounded-host-classes-are-not-universal` (ESTABLISHED): no host class with one recursive word-problem time bound contains every decidable input.
- `rational-homeomorphism-subgroups-have-exponential-wp`: finitely generated groups of rational Cantor homeomorphisms have word problem in time 2^O(n).
- `amenable-full-group-forces-invariant-measure` and `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`: in amenable measure-preserving orbit structures, Kazhdan subgroups are residually finite. Deligne's lattice is decidable, Kazhdan and not residually finite, so a universal host needs non-amenable orbits.
- `boone-higman-via-rover-nekrashevych-hosts` (dead), through `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` and `baumslag-gersten-embeds-in-no-rover-nekrashevych-group`.
- `derived-full-group-h2-filtered-by-mod-two-groupoid-homology` (ESTABLISHED, unreviewed): for a minimal ample groupoid with comparison, infinite H_2(G), H_1(G; Z/2) or H_0(G; Z/2) rules out finite presentation of D([[G]]).
- `fp-subshift-full-group-subgroups-extend-to-sft` (ESTABLISHED): a finitely presented subgroup of a free subshift's full group extends isomorphically to an SFT neighbourhood.
- `periodic-approximable-subshifts-host-no-fp-simple-group` (ESTABLISHED). The Labbé and Penrose finite-presentation nodes are OPEN.
- `fp-full-binary-cantor-groups-have-type-a-actions`: a finitely presented full Cantor group containing standard binary V has a type (A) action.

## Sources checked

Abstract level unless stated otherwise.
- **Matui, arXiv:1210.5800.** For one-sided irreducible SFT groupoids, [[G]] "is of type F_∞, and so in particular it is finitely presented". D([[G]]) is simple for almost finite or purely infinite groupoids.
- **Matui, arXiv:1512.01724** (products of SFT groupoids). Computes homology, K-groups and the abelianization of the full groups. States no finite presentation.
- **arXiv:2105.02183** (Higman–Thompson-like groups of higher rank graphs). Simplicity of the commutator group and related properties. No finiteness statement.
- **Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224.** "every full, contracting RSG embeds in a finitely presented simple group" (abstract, verbatim).
- **Nekrashevych, arXiv:1511.08241.** A(G) is simple for minimal groupoids of germs and finitely generated for expansive groupoids. Nothing on finite presentation.
- **Nekrashevych, arXiv:1312.5654.** The groups of locally expanding self-coverings of compact path-connected spaces are finitely presented. From a search summary only.
- **Farley–Hughes, arXiv:1206.2692.** A class of FSS groups is of type F_∞. From a search summary only.
- **Grigorchuk–Medynets, arXiv:1105.0719.** [[T]]' is infinitely presented for Cantor minimal Z-systems, and topological full groups are locally embeddable into finite groups.
- **Li, arXiv:2209.08087.** Homology of topological full groups through groupoid homology; the AH conjecture for minimal ample groupoids with comparison.
- **Gao–Jackson–Seward.** Every countable group admits a free subshift on {0,1}. From a search summary only.
- **Künneth formula** for homology of products of étale groupoids: arXiv:2310.09928, from a search summary only, not read.

## Approach 1. Finite-type groupoid full groups as universal hosts

**Idea.** In this lens, the full groups with known finite-presentation criteria are:
- one-sided irreducible SFT groupoids (Matui, F_∞);
- Brin–Thompson nV (products of full shifts);
- FSS groups (Farley–Hughes);
- full contracting rational similarity groups (BBMZ);
- groups of expanding self-coverings (Nekrashevych).
They are finitely presented and have simple commutator subgroups. Higher-rank-graph groupoids are the natural next family. Use one of them as a universal host.

**Would prove.** Boone–Higman, if every decidable input embedded in one host.

**Kill test (hand computation).** Each element acts by finitely many coordinatewise prefix-replacement rules on cylinder sets of a finite-alphabet path space. A product of n generators has a rule table with at most C^n rules of prefix length at most Cn, so deciding equality takes time 2^{O(n)}. The bound has the same shape for every host, with host-dependent constants. So `complexity-bounded-host-classes-are-not-universal` (with T(n) = 2^n) excludes every member of the class as a universal host. The same count applies to full groups of higher-rank-graph and product-of-SFT groupoids.

**Verdict.** Killed as universal hosts. Kept as finite-presentation building blocks.

## Approach 2. Katsura–Exel–Pardo and Scott-type self-similar graph groupoids with a finitely presented vertex group

**Idea.** Scott's criterion (V_d(H) is finitely presented when H is a finitely presented self-similar group; imported in `rover-nekrashevych-finite-presentation-criteria-citation`) has no finite-state hypothesis. So germs can carry the algorithm of an arbitrary finitely presented group. Graph generalizations enlarge the class: Exel–Pardo groupoids of a finite graph with a self-similar group action and cocycle, whose full groups generalize Higman–Thompson groups.

**Would prove.** Boone–Higman for inputs that embed in a finitely presented self-similar group over a finite graph.

**Kill test.** The dead-route obstructions on main: Kazhdan subgroups of V_d(H) are residually finite while Deligne's lattice is not, and Baumslag–Gersten embeds in no V_d(H). The Kazhdan argument goes through the locally finite rooted tree of cones. The path space of a finite graph still has such a tree. I checked the transfer by hand but have not written it as a proof.

**Verdict.** Killed as universal hosts, with the transfer of the Kazhdan mechanism not written out.

## Approach 3. Transformation groupoids of a non-amenable finitely presented group on a minimal subshift

**Idea.**
- By Clapham, every decidable input G sits in a finitely presented group Λ with solvable word problem.
- By Gao–Jackson–Seward, Λ has a free subshift, hence a free minimal subshift X. Then Λ ≤ [[Λ ⋉ X]].
- The orbits are non-amenable when Λ is non-amenable, avoiding the amenable-orbit Kazhdan obstruction.
- The groupoid carries Λ's global language and is not finite-state, so no uniform complexity bound applies.
- A(Λ ⋉ X) is simple (minimal) and finitely generated (expansive), by Nekrashevych.

**Would prove.** Boone–Higman, if A(Λ ⋉ X) or D([[Λ ⋉ X]]) is finitely presented for some such X and contains a copy of G.

**Kill test.**
- (a) The Grigorchuk–Medynets LEF mechanism uses amenable Z-towers. I found no analogue for non-amenable Λ.
- (b) The homology precondition from `derived-full-group-h2-filtered-by-mod-two-groupoid-homology` needs finite H_0(Λ ⋉ X; Z/2) (the coinvariants of C(X, Z/2)), finite H_1(·; Z/2) and finite H_2. None of these is computed for any free minimal subshift of a non-amenable group, and the comparison hypothesis is also unchecked.

**Verdict.** Unclear. The missing input is a finite-presentation criterion for A(G) of expansive minimal groupoids coming from group actions rather than expanding maps.

## Approach 4. Stabilize by the full 2-shift: G_2 × (Λ ⋉ X)   [best lead]

**Idea.** Take the product with the one-sided full 2-shift groupoid G_2, whose full group is Thompson's V. Several consequences come cheaply.
- **Homology vanishes.** H_*(G_2) = 0 in all degrees (H_0 = coker(1 − 2) = 0 and H_1 = ker(1 − 2) = 0, from Matui's SFT formulas, not re-read). By the Künneth formula, H_*(G_2 × H) = 0 for every H, so the mod-2 obstruction of `derived-full-group-h2-filtered-by-mod-two-groupoid-homology` vanishes identically.
- **The full group is simple.** If G_2 × H is minimal with comparison (pure infiniteness should come from the G_2 factor; unchecked), Li's AH theorem gives [[G_2 × H]]^ab = 0. So the full group is perfect, equals D, and is simple.
- **The input lands inside.** H = Λ ⋉ X acts in the second coordinate, so G ≤ Λ ≤ [[G_2 × H]] = D.
- **Finite generation.** Expansiveness passes to the product, so A = D is finitely generated (Nekrashevych).
- **No complexity kill.** Germs in the H-coordinate are not finite-state.
- **No LEF obstruction.** D contains V, so the Grigorchuk–Medynets mechanism can't apply.

This mirrors the Leavitt tensor hosts on main (`leavitt-tensor-hosts-acyclic-steinberg-and-fp`): tensoring with L_2 kills K-theory, and here taking a product with G_2 kills groupoid homology.

**Would prove.** Boone–Higman, if D([[G_2 × (Λ ⋉ X)]]) is finitely presented.

**Kill test (hand, run now).** The obvious Brown-criterion complex is built from coordinate-1 cylinder partitions. The stabilizer of a vertex with k pieces is roughly Sym(k) ⋉ [[H]]^k. Brown's criterion needs those stabilizers to be of type F_2, which means finite presentation of [[H]] itself, i.e. Approach 3. So the naive product complex is circular, and a mixed complex whose simplices also refine in the H-coordinate is needed.

**Next test.** Use the smallest non-expanding factor: H = Z ⋉ X for a minimal Z-subshift (Sturmian or Toeplitz). D([[H]]) is infinitely presented (Grigorchuk–Medynets), so either answer is informative.
- Proving that D([[G_2 × (Z ⋉ X)]]) is finitely presented would be a genuine stabilization theorem.
- Proving it isn't, through a new obstruction that survives vanishing groupoid homology, would kill this approach.
No literature on this group was found.

**Verdict.** Survives: unclear, and the best lead in this lens.

## Approach 5. A "finitely many patterns" obstruction for finitely presented full groups of subshift products

**Idea.** Turn `fp-subshift-full-group-subgroups-extend-to-sft` into a necessary condition. If D([[G_2 × (Λ ⋉ X)]]) is finitely presented, it extends isomorphically to a group acting on X_2 × Y for an SFT Y ⊇ X. Combine that with the isomorphism rigidity of full groups of minimal groupoids (Matui) to force X to be of relatively finite type.

**Would prove.** Either an obstruction that kills Approach 4 for minimal X not of finite type, or a proof that X must be of finite type. The latter would need minimal free SFTs on Λ, whose existence for self-simulable groups is not established in the sources checked.

**Kill test.** The extended group acts on X_2 × Y, which is not minimal, so the rigidity theorems stated for minimal groupoids don't apply. No contradiction obtained.

**Verdict.** Unclear. Weak as an obstruction, useful as a design constraint: take X of finite type when possible.

## The exact missing input

A finite-presentation criterion for derived full groups of minimal expansive ample groupoids that are not finite-state in some direction, e.g. G_2 × (Λ ⋉ X). A plausible shape: finite generation, vanishing low groupoid homology, and a mixed-coordinate refinement complex with highly connected descending links together imply finite presentation.

Every known criterion in this lens is either finite-state or built on a locally finite cone tree: Matui SFT, Brin nV, Farley–Hughes FSS, BBMZ contracting RSGs, Nekrashevych expanding maps, Scott V_d(H). Existing nodes exclude both classes as universal hosts.
