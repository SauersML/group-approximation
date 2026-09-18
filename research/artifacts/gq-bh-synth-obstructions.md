# What the Boone–Higman obstructions have in common (bh-synth-obstructions, 2026-09-18)

This is a synthesis of the obstruction and exclusion nodes landed on 09-17/18, read from origin/main at
22bb0eb3d plus board/LESSONS.md. It reads the obstruction side for **general** Boone–Higman, not for single test
cases.
- The one new theorem is `zero-set-confinement-unifies-host-obstructions` (lane proof, elementary).
- The other principles are standard facts, cited as such.
- Everything below that is labelled heuristic or conjectural is exactly that.

## 0. Summary
1. **Three mechanisms explain essentially every obstruction.**
   - **(Z) zero-set confinement:** a rigid or distorted feature of the input is forced into the zero set of every
     natural stable length of the host.
   - **(R) finite-presentation rigidity:** a finitely presented marked group has a neighbourhood made of its marked
     quotients, so finitely presented hosts are rigid points of their parameter families.
   - **(H) hereditary approximation:** a subgroup-closed property of the host (residual finiteness, LEF, exactness,
     coarse embeddability, a word-problem complexity bound) passes to the inputs.
2. **Four of the six walls these produce are already broken by rank ≥ 2 hosts.** The walls are Haagerup/Kazhdan,
   distortion, residual finiteness, a central-extension wall, an arithmetic wall, and complexity. Rank-one hosts
   are stopped by the first three: V-type groups, germ extensions, Röver–Nekrashevych groups, 1D PL groups,
   automaton groups and Houghton/shell envelopes. Rank ≥ 2 hosts break those three:
   - Ã₂ and tree-product k-graph full groups contain Kazhdan and non-RF lattices;
   - 2V_τ and 3V contain BS(1,m);
   - W contains SL_n(Z), pending verification.
   The arithmetic wall has an algebraic host: St_10(R_L) contains every GL_n(Q), but its central Q^× is not
   finitely generated. The central wall is open.
3. **The complexity wall is the one that is structurally unbroken.** Every finite-presentation certificate we
   have certifies *deterministic* local rules: Li's (UFP*) categories, BBMZ nuclei, Stein–Farley complexes, the
   Brown criterion. Deterministic rules cap the word problem by that of the unit/isotropy groups. And (Z)+(L)
   pushes a Kazhdan input *into* those groups. So with current tools, general BH for the reduced input class
   recurses into itself one level down (§4).
4. **Design consequence.** A universal host needs finite-type local rules that are *non-deterministic*, where the
   extension problem carries computation, as in 2D SFTs. Or it needs a hard finitely presented type (A) actor.
   Symbolic dynamics has exactly one known mechanism that is rigid, finite type and computationally universal at
   once: hierarchical (Mozes / Goodman-Strauss / Durand–Romashchenko–Shen fixed-point) tilings in dimension ≥ 2.
5. **Verdict.** Nothing here suggests BH is false. The obstructions kill *tame* constructions. A genuine
   counterexample needs one uniform property of all finitely presented simple groups (§6). None has any support,
   but the complexity bound is the one today's data cannot rule out.

## 1. The three mechanisms

### (Z) Zero-set confinement — theorem `zero-set-confinement-unifies-host-obstructions`
A stable length is `ν(g) = lim ℓ(g^m)/m` for a subadditive symmetric `ℓ`. Examples:
- translation length;
- the norm of a cocycle, i.e. √(cnd function);
- `|gM △ M|` for a commensurated set, which covers wall counts and near index;
- stable word length.

Such a `ν` is homogeneous and conjugation invariant. Two features always land in its zero set `Z(ν)`:
- **Baumslag–Solitar root groups:** `R(s,u) = ⋃ s^{-k}⟨u⟩s^k`, whenever `sus⁻¹ = u^n` with `|n| ≥ 2`;
- **Rigid subgroups:** (FH) subgroups for cocycle lengths, and FW subgroups for commensurated-set lengths.

A host whose natural `Z(ν)` is small therefore excludes both. **Localization (L)** is (Z) applied to germ or
shell commensurated sets:
- FW/Kazhdan inputs of germ extensions of V land in finitely many singular germ groups
  (`almost-v-fw-subgroups-act-through-finitely-many-germs`), and a simple one lands in *one*
  (`simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`);
- window-zero shells for FW inputs are exactly self-similar actions of finite defect
  (`fw-window-zero-shells-are-self-similar-actions`).

### (R) Finite-presentation rigidity
Standard fact (space of marked groups; recalled from Champetier and Cornulier–Guyot–Pitsch, not re-read): a
finitely presented marked group has a neighbourhood consisting of its marked quotients. Compose this with any
continuous parameter map `p ↦ (Γ_p, A)`. If some relation of `Γ_{p₀}` fails at parameters `p → p₀`, then
`Γ_{p₀}` is not finitely presented. Every "deformation / generic / pinning" kill is this:
- `fp-bieri-strebel-line-groups-are-deformation-rigid` and
  `fp-pl-groups-with-f-have-no-transcendental-support-endpoints`: the parameters must be algebraic;
- `fsym-containing-fp-groups-are-pinned-by-finitely-many-equations`,
  `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` and
  `piecewise-translation-z2-enumerations-are-not-fp`: generic and translation-only enumerations die;
- `block-power-germ-schedules-with-fp-germ-group-are-exponential`: schedules satisfy linear recurrences;
- bh-free-22's lesson: finite presentation of a Thompson-like host is pinned by its short relations.

**Consequence.** A finitely presented host must be a rigid point, i.e. the unique solution of finitely many local
rules. In one dimension such rigid solutions are eventually periodic, regular or algebraic:
- zigzag envelopes are only virtually Houghton;
- finite-ray shells need a virtually cyclic input;
- Pisot/(F) slopes (bh-near-actions);
- affine self-similar groups are function-field linear (bh-free-25).

### (H) Hereditary approximation (`hereditary-approximation-disproofs-of-boone-higman`)
Host properties closed under subgroups:
- **residual finiteness:** linear, self-similar and automaton hosts miss non-RF inputs
  (`sl-n-of-infinite-fields-lie-in-no-residually-finite-group`, `torelli-lower-central-quotients-are-not-residually-finite`,
  the dense-coset wreaths);
- **LEF:** RF Z^N full groups are not fp (`rf-free-minimal-zn-actions-have-non-fp-derived-full-groups`);
- **torsion-RF + Zelmanov:** `almost-automorphism-torsion-subgroups-are-rf` excludes Burnside groups;
- **exactness and coarse embeddability:** class kills, `exactness-separates-boone-higman-iff-fp-simple-groups-exact`
  and `coarse-embeddability-separates-boone-higman`;
- **word-problem complexity caps:**
  - nV is coNP (Birget, recalled);
  - Leavitt tensor units reach one counting quantifier (`leavitt-tensor-unit-word-problems-have-one-counting-quantifier`);
  - finite-unit-group coded hosts are exponential (bh-lattices' lesson);
  - SV_G is its actor's orbit problem (`twisted-brin-thompson-wp-equals-actor-orbit-problem`).

## 2. Host families and the walls they carry
Walls:
- **K** Haagerup/Kazhdan;
- **D** distortion (BS roots, H4, BG);
- **RF** residual finiteness;
- **Z** central extensions that survive on stabilizers;
- **Q** scaling a rational line by all primes;
- **C** complexity.

"wall" means the family cannot host inputs of that kind; "broken" means it hosts some; "open" means undecided.

| Family | K | D | RF | Z | Q | C (cap) | Mechanism of the walls |
|---|---|---|---|---|---|---|---|
| V, Higman–Thompson, finite germ extensions of V | wall (finite, or localized to germ groups) | wall in V | broken (V ⊄ RF) | – | wall | P (V, recalled) | (Z) Farley; (L) germs; undistorted cyclics |
| Röver–Nekrashevych, contracting RSGs | wall (Kazhdan subgroups RF) | partial | wall on the self-similar part | – | wall | low (contracting) | (H) RF of faithful self-similar; bh-algebra retraction wall |
| 1D PL / piecewise projective / Stein | wall for H4 (Lodha–Moore/Monod) | BS yes, H4 no | broken | – | wall (finitely generated ratio characters) | low | (Z) slopes and ratios; (R) algebraic parameters |
| Linear, RF, automaton, almost-automorphism | wall | varies | wall | – | wall (no fg ring ⊇ Q) | low | (H) |
| Proper cocompact CAT(0), Haagerup groups | wall | wall | – | – | – | – | (Z) translation length |
| Houghton-like / shell envelopes (FSym) | wall at window 0 | wall (end counts) | – | – | – | – | (Z)+(L) near index; (R) pinning |
| nV, 2V_τ, twisted SV_G, W | open for nV; W: broken (SL_n(Z)) | broken (2V_τ, 3V) | broken | open | wall so far (mass modules, bh-free-30) | coNP for nV; SV_G = orbit problem | (Z) with non-confined zero sets |
| k-graph / degree-category full groups (Ã₂, tree products, CT_P(Z)) | **broken** (Ã₂ (T) lattices) | – | **broken** (non-RF tree lattices) | wall on boundaries (bh-lattices untwisting) | – | exp with finite unit groups | (Z) confinement fails; (R) via Li (UFP*) |
| Leavitt / Steinberg units (St_N(R_L), EL_n(L)) | broken (Kazhdan) | – | – | wall: centre Q^× not fg | broken inside St_10(R_L) | ≤ one counting quantifier | (H) centre finiteness; FW shell windows |
| Z^d-action full groups (amenable) | ? | ? | LEF when RF, so not fp | – | – | unknown (conjecturally ≥ the language of X) | (H); non-RF case open (Matui) |

## 3. The rank picture
- **Rank one.** In rank one (tree / Cuntz / 1D dynamics), every wall except RF holds, and they hold for one
  reason: the natural stable lengths have *confined* zero sets. V's zero-entropy, zero-drift and no-attractor
  elements are torsion, and V is Haagerup.
- **Rank ≥ 2.** Here the zero sets stop being confined. Every positive result of 09-18 on a hard feature is an
  element or subgroup of a non-confined zero set:
  - the 2V_τ odometer: zero exponent sums, no periodic points, BS(1,2) (`odometer-2v-is-fp-simple-and-contains-bs12`);
  - SMART_m in 3V: zero entropy, height-m renormalization (`bs-1-m-embeds-in-brin-thompson-3v-for-odd-m`);
  - Kazhdan Ã₂ lattices acting genuinely on a rank-two boundary (`a2-lattices-embed-in-fp-simple-groups`);
  - non-RF tree lattices (`cocompact-tree-product-lattices-lie-in-type-a-class`);
  - Boshernitzan's minimal element in Stein groups: rotation-like, no hyperbolic periodic point.
- **The counterpart lesson (bh-free-36).** Hosts must match the rank of the input's flats: rank-one codings fail for
  any group with product regions.

## 4. The last wall: complexity, and the recursion trap
- **The requirement.** `complex-fp-simple-groups-from-boone-higman`: BH forces finitely presented simple groups
  beyond every recursive time bound. That is `fp-simple-groups-with-arbitrarily-complex-word-problem`, which is
  OPEN. So a universal host family must have unbounded word-problem complexity.
- **What the certificates give.** Every finite-presentation certificate in the repo certifies local rules that are
  *deterministic*: every locally admissible finite pattern extends. Li's (UFP*) degree categories have unique
  factorization and no dead ends, so their path languages are trivial to decide. BBMZ nuclei, Stein–Farley
  complexes, and the Zaremsky and Brown criteria are the same.
- **The cap.** So the host's complexity is at most (unit/isotropy/actor complexity) × exponential:
  - bh-lattices: finite unit groups cap at exponential;
  - `twisted-brin-thompson-wp-equals-actor-orbit-problem`.
- **The trap (recursion).** By (Z)+(L), a Kazhdan input with a hard word problem cannot sit in the deterministic
  part, because the complexity is too high there. It is forced into a unit group, a singular germ group or the
  actor. That group must itself be a finitely presented overgroup with the same hard word problem, embedded in a
  host of the same kind. The two nodes below state this in its sharpest form: germ-type BH is equivalent to
  realizing each simple Kazhdan input in one fp germ group together with a dilation, and the host's global shape
  adds nothing.
  - `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`;
  - bh-kazhdan-inputs' lesson.
- **Two ways out, and only two.**
  1. **A hard finitely presented type (A) actor.** Then SV_G is fp simple with that hardness. Premise:
     `explicit-type-a-actor-with-non-pr-orbit-problem`, which is OPEN; four 7.19 attempts have landed kills.
  2. **Finite presentation for non-deterministic finite-type dynamics.** Here the extension problem of a
     finite-type rule set (a Z²-SFT) carries the computation. Berger/Robinson: 2D local rules can force aperiodic,
     computing configurations. Hochman / Aubrun–Sablik / Durand–Romashchenko–Shen: effective 1D subshifts are
     projective subdynamics of 2D SFTs, and fixed-point tilings are self-similar *and* universal (recalled, not
     read here).
- **Why dimension 2 matters.** In dimension 1, finite-type means regular. In dimension ≥ 2 it can mean universal.
  This is the same dichotomy as (R)'s "rigid solutions in 1D are periodic or algebraic".

## 5. Design specification for a host of the reduced input class
The target is: infinite fg simple Kazhdan S with solvable WP (`boone-higman-iff-simple-kazhdan-decidable-inputs`),
plus H4, BG, Deligne's lattice, Q_{g,c} and GL_n(Q). The host D must:
- **D1 (non-confined rigidity).** Carry no stable length of type cocycle or commensurated-set whose zero set is
  confined on the carrier of S. Equivalently S must act *genuinely*: with unbounded orbits on no wall structure,
  yet not through finitely many germs. Rank ≥ 2 boundary-type actions do this (Ã₂).
- **D2 (renormalizable zero-entropy elements).** Contain infinite-order elements with zero entropy, zero drift and
  no hyperbolic periodic points (odometer or SMART type), so that BS roots, H4 and BG are possible.
- **D3 (rigid).** Be a rigid point of a finite-type family: finitely presented by finitely many *local* rules, per
  (R). Non-generic, non-deformable data.
- **D4 (universal).** Have unbounded word-problem complexity across the family. By §4 this needs either
  non-deterministic finite-type local rules or a hard fp type (A) actor. It is *not* reachable by UFP-type
  categories with tame unit groups.
- **D5 (outside every tame hereditary class).** Not RF or LEF, and not exact or coarsely embeddable somewhere in
  the family (class kills). Test: does the family contain Osajda's decidable non-exact group?
- **D6 (centre and arithmetic).**
  - For Deligne-type and Q_{g,c}-type inputs, the central class must be carried by isotropy, not by a boundary
    cover (`central-extension-untwisting-over-boundaries`).
  - For GL_n(Q), the scalars Q^× must not become a non-fg centre (`leavitt-scalar-commutators-block-fp-central-quotients`).
  - Scalings of a rational line must not factor through finitely generated local ratio data (mass modules,
    ratio characters).

**Must avoid:**
- finite germ extensions of V as the place where S sits;
- faithful self-similar or retracting bases;
- one-dimensional PL, piecewise projective and rotation data;
- Haagerup or proper-CAT(0) ambient structure;
- generic or deformable parameters;
- deterministic local rules plus tame unit groups for hard inputs.

**Master candidate (conjectural).** A "rank-2 contracting similarity groupoid":
- **Space:** the groupoid of partial similarities of a hierarchical finite-type tiling space, e.g. a
  Durand–Romashchenko–Shen fixed-point tiling programmed with S's word-problem algorithm, stabilized by O₂.
- **Why each property should hold:** the hierarchy should give the BBMZ-style nucleus (D3); the finite-type
  matching rules should carry the computation (D4); S should act by rank-two moves (D1); the odometer structure
  of the hierarchy supplies D2; Matui simplicity comes from minimality plus pure infiniteness.
- **What is open:** whether such groupoids admit an F_2 / finite-presentation certificate at all. That is the
  decisive technical question.

## 6. Could BH be false? What a counterexample needs
- **What a counterexample must be.** By `bh-separators-must-omit-nested-decidable-hosts`, a counterexample is a
  subgroup-closed property P holding for every fp simple group and failing for some fg decidable group. Such a P
  must also omit a simple Kazhdan decidable group inside an fp decidable group.
- **The surviving candidates** (everything else is killed on main):
  1. a uniform recursive bound on the word problems of fp simple groups;
  2. exactness of all fp simple groups;
  3. coarse embeddability of all fp simple groups.
- **What today's data say.** Every fp simple group we can analyse has WP ≤ coNP^⊕P-type or ≤ exponential over its
  actor. Every host we built is a full group of an *amenable* groupoid or a Leavitt unit group. That is
  consistent with (1) and with (2)–(3). But it is equally the pre-1961 situation for fp groups before Higman: all
  known fp groups were tame, and the tameness was an artefact of the constructions.
- **Honest assessment.** There is no mechanism that would make fp *simple* groups uniformly tame. Simplicity via
  Matui is a local dynamical property, and nothing in its proof bounds complexity. So the obstructions give no
  evidence for falsity. They do show that a proof must contain a genuinely new *finite-presentation theorem for
  universal (non-deterministic) finite-type dynamics*, or a hard fp type (A) actor.
- **Sharp open diagnostic (Q-exact).** Are topological full groups of amenable ample groupoids exact?
  - If the input's germ subgroupoid inherits amenability, which is automatic when it is closed (ADR's closed
    subgroupoid theorem, recalled), the input is exact.
  - So a yes-type answer would force a universal route to use *non-amenable* groupoids to reach Osajda's group.
  - Not settled here.

## 7. Agenda, ranked by leverage on general BH
1. **Complexity wall, non-deterministic finite type.** Matui's question for minimal *aperiodic* Z²-SFTs (Robinson,
   DRS). Is D([[Z² ⋉ X]]) finitely presented? If so, is its WP at least the language complexity of X? Node
   `free-minimal-zn-derived-full-groups-are-never-fp`; bh-free-12 owns the non-RF case. A yes gives the first fp
   simple groups from computation-capable tilings and attacks `fp-simple-groups-with-arbitrarily-complex-word-problem`.
2. **Complexity wall, actor route.** A finitely presented group with a type (A) action and hard orbit problem
   (`explicit-type-a-actor-with-non-pr-orbit-problem`, `kourovka-7-19-via-hard-type-a-actor`).
3. **Rank-2 nucleus theorem.** Extend BBMZ Theorem A (contracting ⇒ fp full group) from trees to finite-type
   rank-2 categories *without* (UFP*). This is the certificate D3 needs. bh-groupoid and bh-lattices have the
   machinery.
4. **Q-exact** (§6). It decides whether amenable groupoids can carry the conjecture at all.
5. **Kazhdan genuine actions in Brin–Thompson rank:** `kazhdan-subgroups-of-brin-thompson-groups-are-finite`
   versus `every-gl-n-z-embeds-in-some-brin-thompson-group`, and bh-verify-W on W ⊇ SL_n(Z). This decides whether
   nV-rank hosts already break the K wall.
6. **Central wall:** a host carrying Deligne's class in isotropy (bh-free-55's 2V_Λ(n) plus finite presentation).

## 8. Trust
- The (Z) theorem is proved in its node.
- (R) is the standard marked-groups fact (recalled).
- The table cells cite nodes that are mostly unreviewed lane proofs; W is pending bh-verify-W.
- Recalled, not read here: Birget's coNP bound; the symbolic-dynamics results (Berger, Robinson, Mozes,
  Goodman-Strauss, Hochman, Aubrun–Sablik, DRS); ADR's closed-subgroupoid amenability.
- The master candidate in §5 is a conjecture, not a result.
