# Boone–Higman swarm: general lessons (09-18, second summary)

Lane `bh-writeup`, 2026-09-18, written from the node texts on main at `b2b4b26f6`
(10:51 CDT).
- This pass covers the 268 landings since `27bee4278` (09:46–10:51): 285 new or edited
  nodes, of which 222 are ESTABLISHED, 38 OPEN and 5 REFUTED or DEAD.
- Following the 10:48 user order, it is organized by mechanism: what each cluster
  teaches about proving BH in general.
- The case ledger for the first 226 landings is the previous version of this file
  (`27bee4278`). §3 updates its table of named problems.

**Status tags.**
- **[LP]** lane proof, checked only by the lane that wrote it.
- **[IC]** internal adversarial check by another lane (bh-refute, bh-free-43, bh-free-48,
  bh-verify-W).
- **[RA] / [RB] / [RC]** passed by gq-referee-a (proof gaps), gq-referee-b (citations) or
  bh-referee-c (end to end).

None of these is an external review. Priority checks were arXiv-only, and no entry claims
novelty. **Most entries are [LP].** The root `boone-higman-conjecture` stays OPEN.

## 1. The picture

Every positive result on main now factors through two layers.

1. **A wrapper** turns an actor into a finitely presented simple group. Examples are
   twisted Brin–Thompson groups SV_G, Cuntz-stabilized full groups, and finite germ
   extensions of V. This layer is now essentially understood (L1).
2. **An actor**: a finitely presented group with a type (A) action that contains the
   input. All the difficulty sits here, and this pass shows why:
   - rigid inputs are never their own actors (L4);
   - finite presentation forces every piece of local dynamical data into a regular form
     (L3);
   - every host family built from fixed finite data has a uniform ceiling on
     word-problem complexity (L2).

So general BH needs a **compiler**. That is an actor built from the input, whose finitely
many local rules are regular but whose global dynamics carry the input's word problem. §5
gives the precise forms of this question that are on main.

## 2. Lessons by mechanism

### L1. The wrapper layer is solved: simplicity and type (A) come free from a finite model

**Mechanism.**
- (i) SV_G is of type F_n exactly when G ↷ S is of type (A_n).
- (ii) Crossing a full group with the Cuntz groupoid O_2 gives comparison of clopen sets.
  The action on clopens is then of type (A).
- (iii) Li's F_∞ theorem applies to finite left-cancellative categories with a degree
  map: k-graphs, Zappa–Szép products, and orbit categories of lattices.

**Evidence.**
- `twisted-brin-thompson-type-fn-criterion` [RA] proves the conjecture of Belk–Zaremsky,
  2001.04579, l.218. With it, `stein-complex-elementary-intervals-are-grid-spheres` [RA].
- `stabilized-kgraph-full-groups-have-type-a-actions` [LP] and
  `degree-category-full-groups-stabilized-have-type-a-actions` [LP].
- **Payoffs.**
  - Every cocompact Ã₂ lattice, exotic or not, torsion allowed:
    `exotic-a2-lattices-satisfy-boone-higman`, `a2-lattices-lie-in-permutational-bh-class`,
    `a2-lattices-embed-in-fp-simple-groups` (an F_∞ simple host) [LP].
  - Every cocompact lattice on a product of trees, torsion allowed:
    `cocompact-tree-product-lattices-lie-in-type-a-class` [IC]; also
    `tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh` (Amir–Lazarovich) [LP].
  - RCWA groups over Z, over class-number-one number rings, over F_q[t] and over Z_(π):
    `rcwa-groups-satisfy-permutational-boone-higman` [RA][IC].
  - CT_P(Z) acts on N_0 with type (A) [LP].

**Lesson for general BH.** A group has a finite combinatorial model of an effective
boundary action (a finite category with a degree map) ⇒ the group lies in B_A. Building
the model is the whole task; the wrapper supplies simplicity and finite presentation.
Kohl's problems (§3) show the same thing from the other side: identifying CT(Z) as a full
group imported Matui's rigidity and Li's finiteness at once.

**Where it stops.**
- **Effectiveness.** The decorated Garside groupoid is not effective. The Artin group
  lands in isotropy, and no simple subgroup contains it
  (`garside-decorated-groupoids-hide-artin-groups-in-isotropy` [LP]; that route is DEAD).
- **Coefficients.** As proved, the stabilization theorem needs finite unit groups, so
  infinite coefficient groups are not yet covered.
- **Complexity** (L2).

### L2. Complexity ceilings: hosts built from fixed finite data cannot be universal

**Evidence.**
- Finitely generated subgroups of finite k-graph full groups, nV included, have at most
  exponential word problems (earlier node).
- Units of Leavitt tensor algebras have word problems in ∀·Mod_pP or C_=P
  (`leavitt-tensor-unit-word-problems-have-one-counting-quantifier` [LP]).
  (L ⊗ L)^× is coNP^⊕P-complete (`leavitt-square-units-have-conp-parity-p-complete-word-problem`
  [LP], mathematics cross-checked by bh-free-02). The C_=P-complete group Γ_Z has no
  Leavitt-linear simple host [LP].
- Finitely presented piecewise-projective groups with arbitrary real data specialize to
  algebraic data, so they have solvable word problem
  (`fp-piecewise-projective-groups-specialize-to-algebraic-data` [LP]). Hard-slope D(V_λ)
  embed in no finitely presented piecewise-projective group [LP].
- Self-similar affine groups are linear over function fields
  (`affine-self-similar-groups-are-function-field-linear` [LP]). KMS configuration modules
  have trivial coinvariants [LP], so KMS tops get no self-similar affine host.
- **Hard inputs are cheap.**
  - `transcendental-slope-thompson-groups-have-hard-word-problems` [LP]: 2-generated
    simple groups D(V_λ) whose solvable word problem exceeds any recursive bound.
  - F.p. residually finite groups with a non-primitive-recursive word problem exist (KMS,
    literature; Kourovka 5.15).

**Lesson for general BH.** Boone–Rogers already rules out a single universal host. The
ceilings rule out more: any host family defined by fixed finite algebraic data (a ring, a
k-graph, a field of definition, an automaton) specializes, so its finitely generated
subgroups have word problems in a fixed class. A proof of BH must use data that grow with
the input. Three sources are in view:
- an input-dependent coefficient group (L1, "Coefficients");
- an input-dependent enumeration (the shells, L6);
- an input-dependent type (A) actor.

Kourovka 7.19 is the concrete test. Routes `kourovka-7-19-via-small-cancellation-bh` and
`kourovka-7-19-via-hard-type-a-actor` are open.

### L3. Finite presentation forces regular local data; complexity must come from composition

**Evidence: local data get pinned.**
- **Enumerations:** `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` [LP].
- **Germ schedules satisfy linear recurrences:**
  `block-power-germ-schedules-with-fp-germ-group-are-exponential` [LP].
- **Germ rates:** `germ-rate-homomorphism-tests-germ-extension-finiteness` [LP].
- **Normalizers are Cobham-regular:** `ct-z-normalizers-are-2-and-3-regular` [LP]. This
  gives Out(CT(Z)) = C_2.
- **Slopes are algebraic:** `fp-bieri-strebel-line-groups-are-deformation-rigid` and
  `fp-pl-groups-with-f-have-no-transcendental-support-endpoints` [LP].
- **Freeness is the tempting shortcut, and it fails in both frameworks.**
  - Free-shift enumerations pass the Houghton germ gate, but no envelope is finitely
    presented (`free-shift-houghton-like-envelopes-are-not-fp` [RA][IC]).
  - Residually finite groups get free-product germs G ∗ Z over V
    (`rf-groups-have-free-product-germs-over-v` [LP]). This passes the germ gate even for
    KMS groups, but then the one-point SingFix group is not finitely presented
    (`annular-free-factor-germ-extensions-fail-bhm-singfix` [LP]).
- **Regular enumerations reach only virtually cyclic or virtually abelian inputs:**
  `strand-map-bases-lift-only-bounded-displacement-letters`,
  `lampshuffler-bases-lift-no-shift-for-one-ended-inputs`,
  `piecewise-translation-z2-enumerations-are-not-fp`, and
  `zigzag-houghton-like-envelopes-are-virtually-houghton` [LP].

**Lesson for general BH.** An input's complexity cannot be stored in local data. It has
to emerge from composing finitely many regular rules, as in Higman's embedding. The only
mechanism on main that does this inside a fixed finitely presented host is reversible
machine dynamics.
- SMART-type machines give height-m renormalizations in 2V, hence BS(1, ±m) ≤ 3V for
  every odd m (`bs1m-embeds-in-3v-for-every-odd-m` [IC]; an exhaustive certificate covers
  m = 3, …, 11).
- The SMART trace full group, a Juschenko–Monod group, lies in 2V.
- A compiler for BH is therefore more likely to be machine-like than data-like.

**Where it stops.**
- BS(1, 2) ≤ nV (even m) is OPEN.
- In brick hosts, images of Higman's group satisfy E(N) = O(log N · (log log N)²), while
  every aperiodic element of nV has lim sup E(N)/log N ≥ 1/(2n) [LP]. A growth-gap theorem
  between these bounds would exclude Higman's group from every brick host.

### L4. Rigid inputs are never their own actors; the actor is always a Thompson-like overgroup

**Evidence.**
- Infinite locally quasiconvex hyperbolic groups, surface groups and closed hyperbolic
  3-manifold groups have no type (A) action
  (`locally-quasiconvex-hyperbolic-groups-have-no-type-a-actions` [LP]).
- Virtually cyclic subgroups of Out(F_n) have infinitely many double cosets. Subgroups
  with finitely many double cosets have dense limit sets [LP].
- Building-open subgroups of Kac–Moody lattices have infinite bi-index [LP].
- St_N(R_L) has no type (A) action [LP].
- The Baumslag–Gersten group is highly transitive and MIF, yet every action of it with
  finitely many orbits of pairs has an infinitely generated stabilizer [LP].
- For S × T, a type (A) action comes from one of the factors [LP].
- **The general tool:** `escaping-invariant-sets-force-infinitely-many-double-cosets` and
  `limit-set-escaping-forces-infinitely-many-double-cosets` [LP].
- **Geometry is no obstruction.**
  - Hyperbolic groups, Aut(F_n) and their finite products embed quasi-isometrically in
    finitely presented simple groups [LP].
  - Virtually compact special groups and RAAGs are undistorted in 2V [LP].
  - SV_G quasi-retracts onto G (literature).

**Lesson for general BH.** Type (A) needs finitely generated infinite-index subgroups with
finitely many double cosets. Negative curvature, building rigidity and the structure of
St_N(R_L) forbid them. So the actor is never the input. Since hosts can be undistorted,
only finiteness and complexity obstruct BH, not coarse geometry.

### L5. Permanence reduces to one notion: good, centralizer-realizable subgroups

**Evidence.** `pbh-coset-wreaths-iff-identity-edge-hnns` [LP] shows that for G ∈ B_A and
C ≤ G the following are equivalent:
- the lamplighter over G/C lies in B_A;
- the identity-edge HNN over C lies in B_A;
- C is a centralizer C_G(m) for some m in a B_A-overgroup.

Applications:
- `pbh-graphs-of-groups-over-realized-good-edges` [LP];
- centralizer amalgams [LP]. Through Kharlampovich–Myasnikov's iterated extensions of
  centralizers, these give limit groups over torsion-free hyperbolic groups [LP];
- virtual retracts are good (`virtual-retracts-satisfy-pbh-coset-wreath-closure` [LP]),
  which gives wreaths over cosets of f.g. subgroups of limit groups and of free, virtually
  free and Fuchsian groups;
- `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` [LP], so Z wr_X PSL_2(Z[1/2]) embeds
  in a finitely presented simple group;
- the non-RF double of PSL_2(Z[1/2]) along PSL_2(Z) [LP];
- cusp extensions of relatively hyperbolic groups [LP].

**The Mihailova test.** In `fibre-products-over-b-a-quotients-lie-in-cr` [LP], the fibre
product P ≤ F × F over Q is good when Q ∈ B_A and is not good when Q has unsolvable word
problem. The logic lane's hypothesis MH (`fp-embeddability-index-set-is-sigma-3-complete`)
concerns the same Mihailova HNN extensions H(Q). One object is the test case in both
lanes.

**Lesson for general BH.** Permanence under HNN extensions and amalgams, the engine of
Higman-style embeddings, is the problem of realizing edge groups as centralizers inside
one B_A group. The open core is subgroups with decidable membership that are neither
centralizers nor retracts. `pbh-closed-under-decidable-permutational-wreaths` (OPEN)
states it, and its hypothesis is shown necessary.

**Where it stops.** Higman's group. Retracts inherit proper-power conjugacy, so its
splittings have no retract edges, and the closure theorems cannot reach it
(`retracts-inherit-proper-power-conjugacy` [LP]).

### L6. The shell compiler: the FW window theorem says exactly what a Kazhdan input must have

Recall that BH is equivalent to BH for simple Kazhdan decidable inputs.

**Evidence.**
- For FW inputs, shell window zero holds only with sign −1, through an injective
  endomorphism ψ of infinite index (`fw-inputs-pass-window-zero-only-via-proper-self-embeddings` [LP]).
- Moreover:
  - the core of ψ is trivial [LP];
  - C_P(ψ(P)) has finite exponent [LP];
  - co-Hopfian FW inputs fail, and so do automorphism twists (referee-a PASS with a scope
    fix) and every window with pairwise commuting copies [LP].
- `shell-envelopes-depend-only-on-the-near-image` [LP]: the shell route is a question
  about finitely generated subgroups of NearSym_0(N), and realizability is never the
  obstruction.
- **Diagnostics on the natural inputs.**
  - EL_n(L_2) is simple Kazhdan with a trivial-core corner endomorphism, but corner
    endomorphisms have large centralizers [LP].
  - The twists of St_N(R_L) fix its central K_2 ≅ Q^×, so their cores are nontrivial, and
    a torsion-free center fails commuting windows [LP].
- **Algebra gate.**
  - Shell germ Steinberg algebras are never simple, but modulo the singular ideal J they
    are central simple [LP].
  - J is generated at the singular point, as the annihilator of the shell module at
    infinity [LP]. For the zigzag shell of Z, J is finitely generated [LP].
- **Calibration.** V's binary shell passes both germ gates [LP]. Whether its envelope is
  finitely presented is OPEN.
- bh-shell-kazhdan found no obstruction specific to (T): every constraint found depends
  only on one-endedness, and Z² passes.

**Lesson for general BH.** For the inputs that carry BH, a window-zero shell needs an
injective endomorphism ψ with:
- infinite index;
- trivial core;
- an image with a finite-exponent centralizer.

That is a self-similar but not corner-type endomorphism. It is a single algebraic target:
find one infinite simple Kazhdan decidable group with such a ψ, or prove none exists
(which would kill window-zero shells for BH). Wider windows remain only in non-commuting
form.

### L7. Central extensions: the class must die on the germ groupoid while the center survives

**Evidence.**
- Odometer and shear lifts: T_m → T_(m+2) [LP].
- The untwisting criterion (finite kernels): the class must die on every point
  stabilizer, and Cuntz stabilization cannot remove this [LP].
- Deligne's class dies on Lagrangian Cantor covers. It survives on every linear rational
  projective host, by Margulis superrigidity [LP].
- A Leavitt swindle kills Deligne's center in every ring-induced host [LP].
- Deligne's lattice lies in the f.g. simple commutator subgroup of the Lagrangian
  Brin–Thompson group [LP]. Its finite presentation is OPEN.
- For n = 2, unimodular Maslov cells do not dissect mixed atoms, so tree-pair
  presentations do not transfer [LP].
- Torelli lower-central quotients are non-RF Kazhdan groups with solvable word problem
  and contain Deligne-type lattices [LP].

**Lesson for general BH.** The non-RF Kazhdan test groups are central extensions, and the
mechanism is cohomological. The host action must kill the class in H² of its groupoid
while the extension stays injective.
- Linear, rigid actions never kill the class.
- Ring-induced hosts kill the center itself.
- So the host must be piecewise (Maslov cells), and one finite-presentation question is
  the gate.

### L8. Linear groups: finitely many primes go through Thompson-type hosts; all primes need the Leavitt ring

**Evidence.**
- The twisted integral-affine Brin–Thompson group W is finitely presented, simple and
  contains every GL_n(Z). Its S-integral version W_(P,l) has a simple finitely presented
  commutator subgroup containing every GL_n(Z[1/P]) [IC: bh-verify-W PASS].
- For infinitely many primes:
  - no homeomorphism shifts ℓ-adic scalar actions along a chain of six primes (conditional
    on Serre's six exponentials) [LP];
  - no free Q_odd action has a doubling intertwiner [LP];
  - Q ⋊ ⟨2⟩ in 2V_τ reduces to one circle coding [LP].
- **Leavitt resolvent.**
  - K_2-stability holds [RA][RB], so St_N(R_L) has solvable word problem.
  - St_N(R_L) is quasisimple and contains every GL_n(Q) [LP]. PE_10(R_L) is simple but not
    finitely presented, since its H_2 is not finitely generated.
  - St_N(R_L) is generated by two copies of itself [LP].

**Lesson for general BH.** Uniform word problem gives a common host, and here it is
realized concretely: one finitely presented simple group for all GL_n(Z[1/P]). A Leavitt
pair makes unstable K-theory equal to stable K-theory (the gq-infinite-primes line in
LESSONS.md). That turns Steinberg groups over purely infinite rings into decidable
finitely presented hosts for all of GL_n(Q). What remains is the wrapper for St_N(R_L),
which is exactly the L6 shell gate.

### L9. Arithmetic dynamics: one unit condition governs the Stein and IET hosts

**Evidence.**
- Stein groups with slope an algebraic unit β with property (F):
  - they are contracting RSGs [RC, PASS with fixes];
  - they are finitely presented, with a finitely presented simple derived subgroup [LP].
- IET and box-exchange groups over Q(β) satisfy BH [LP].
- (F)-unit fields are characterized by isolated-sign units, which excludes Q(√3) [LP].
- Computable modules are necessary (earlier).

**Lesson for general BH.** Finiteness of a symbolic-coding host is an arithmetic
condition on the expanding unit: finite β-expansions. Contracting-RSG structure is the
uniform device that turns such a coding into a type (A) actor. The norm +1 quadratic case
is open.

## 3. Named problems answered or corrected in this pass

| Problem (source) | Result | Node | Status |
|---|---|---|---|
| Kourovka 17.57 (Kohl): Out(CT(Z)) = C_2? | **Yes**; also Out(CT_P(Z)) = C_2 for every nonempty P | `out-ct-z-is-c2`, `out-ct-p-z-is-c2` | [LP][IC] (bh-free-43 PASS) |
| Kourovka 21.74(b)(c) (Kohl): decide finite cycles in CT(Z) | **Undecidable** | `ct-z-finite-cycle-problems-are-undecidable` | [LP]; Kari–Ollinger, which prints proof sketches only |
| Kourovka 21.75 (Kohl) | **Negative**: CT_P1 and CT_P2 generate CT_(P1∪P2) | `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` | [LP], two independent proofs |
| Kohl's factorization conjecture for RCWA(Z) | **Yes** | `rcwa-z-generated-by-class-shifts-reflections-transpositions` | [LP] |
| Belk–Zaremsky conjecture (2001.04579, l.218) | **Yes**: SV_G is F_n iff the action is (A_n) | `twisted-brin-thompson-type-fn-criterion` | [RA] |
| Mallery–Zaremsky Q5.13 | **Yes** for finitely presented, and for F_m, strongly shift-similar G | `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`, `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups` | [RA], [LP] |
| Mallery–Zaremsky Q3.18, as stated | **No** (a non-f.g. example); the f.g. form is OPEN | `infinite-shift-similar-groups-need-not-be-strongly-shift-similar` | [LP] |
| MathOverflow 412219 | **No**: a f.p. decidable G whose E(G) is not recursively presented | `fp-decidable-group-whose-e-is-not-recursively-presented` | [LP][IC] |
| Tarocchi: is [G_3, G_3] simple? | **Yes**, hence for every G_n, n ≥ 3 | `dendrite-rearrangement-group-g3-has-simple-commutator-subgroup` | [LP] |
| Lodha: is S 2-generated? | **Yes**, and so is every f.g. simple circle group containing T | `lodha-simple-group-s-is-two-generated`, `fg-simple-circle-groups-with-t-are-two-generated` | [LP] |
| Tanner (2312.07375), for (F)-unit slopes | **Yes** | `pisot-unit-slope-stein-groups-are-finitely-presented` | [LP] |
| Matui: free minimal Z^N derived full groups never f.p.? | **Yes for residually finite actions**; the rest is OPEN | `rf-free-minimal-zn-actions-have-non-fp-derived-full-groups` | [LP] |
| Almeida–Dantas–de Oliveira-Tosti (2609.01868): Z wr_X PSL_2(Z[1/2]) into a f.p. self-similar group? | **No**: the group is not RF. It does satisfy BH (L5) | `z-wr-psl2-z-half-is-not-residually-finite` | [LP][IC] |
| BBMZ-hyperbolic Q1.1, virtually free case | **Yes**, with trivial nucleus | `virtually-free-groups-are-contracting-rsgs` | [LP] |
| Survey 5.3(10), exotic Ã₂ lattices | **BH holds** | `exotic-a2-lattices-satisfy-boone-higman` | [LP] |
| Survey 5.3(13), Artin-adjacent cases | Complex braid groups except G_24, G_27, G_29, G_33, G_34; B(e,e,n); supersolvable arrangements | `complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34` et al. | [LP] |
| Solvable cases | Every free centre-by-metabelian group is linear; FP_∞ soluble groups are PBH | `free-centre-by-metabelian-groups-are-linear`, `fp-infinity-soluble-groups-satisfy-permutational-bh` | [LP], priority not checked beyond a bounded search |
| BBCMP Q1.16, first part | Partial: low-complexity MCGs are continuous automatic; once-punctured MCGs are asynchronously so | `low-complexity-mapping-class-groups-are-continuous-automatic` et al. | [LP] |

**Possible errors found in the literature** (all lane proofs, for expert confirmation):
- FFWZ 2603.24687 Lemma 4.9(i) fails for non-faithful actions, which leaves a gap in
  their non-faithful finiteness proofs. Their answer to Q5.8 does not use it.
- The two-generator torsion criterion in Kojima–Sheng 2603.18410 is false in V [RA].
- In the self-similar representation of 2609.01868, Theorem A, every lamp acts the same
  way, so the representation is not faithful.

## 4. Corrections and refutations in this pass

**Refuted or dead.**
- `garside-odometer-groups-have-simple-finite-index-commutator` is REFUTED, so the
  spherical-Artin Garside route is DEAD (L1).
- `every-real-number-field-lies-in-an-f-unit-field` is REFUTED: Q(√3).
- `kms-configuration-modules-carry-self-similar-structures` is REFUTED.
- `lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map` is REFUTED as a full
  target.
- `e-of-finitely-presented-group-is-recursively-presented` is REFUTED (MO 412219).
- `z-wr-psl2-z-half-embeds-in-fp-self-similar-group` is REFUTED.

**Withdrawn or narrowed.**
- The quadratic IET full-group claim now covers only norm −1 fields, after Cleary was
  read at source. Norm +1 is open.
- `stein-v-groups-act-with-type-a-on-breakpoints` is corrected in the same way.
- The stabilization node's citation of Matui's comparison theorem was replaced by a
  direct proof.
- `ct-p1-and-ct-p2-generate-ct-of-the-union` is marked DUPLICATE.

**Status upgrades.** `exotic-a2-lattices-satisfy-boone-higman`,
`one-fp-simple-group-contains-every-integral-linear-group`,
`twisted-integral-affine-full-group-is-finitely-presented`,
`free-centre-by-metabelian-groups-satisfy-boone-higman`,
`piecewise-canonical-permutations-are-transposition-products` and
`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring` went from OPEN to ESTABLISHED.

**Hygiene.** The 27bee4278 flag on the Kourovka artifact ("automatic" listed as a BH
class) is fixed on main.

## 5. The compiler question: its sharpest forms on main

Each item below is stated on main or follows from the nodes cited. None is a printed
problem unless marked.

1. **Groupoid Higman embedding** (`gq-bh-bh-groupoid-frontier.md`).
   - The question: does every f.g. decidable group embed in [[G ⋉ Λ^∞]] for some
     finitely presented G acting pseudo-freely and self-similarly on a finite k-graph (Li,
     case III)?
   - With L1, this would give PBH once the stabilization theorem is extended to infinite
     coefficient groups. That extension is the first concrete step.
2. **The Kazhdan shell endomorphism** (L6): an infinite simple Kazhdan decidable group
   with an injective endomorphism of infinite index, trivial core and a finite-exponent
   centralizer of its image. The calibration is finite presentation of
   `v-binary-shell-envelope-is-finitely-presented`.
3. **Finitely presented shift-similar overgroups.**
   - The f.g. form of Mallery–Zaremsky Q3.18 (printed) is
     `fg-infinite-shift-similar-groups-are-strongly-shift-similar`.
   - With Q5.13 settled for finitely presented G, a finitely presented strongly
     shift-similar overgroup of an input gives that input a type (A) actor.
4. **Good subgroups** (L5): decidable permutational wreaths. Mihailova subgroups are the
   universal test, and Higman's group is the natural hard instance.
5. **Central-extension gate** (L7): finite presentation of the Lagrangian Brin–Thompson
   group, or `deligne-class-dies-on-some-rational-projective-host`.
6. **The complexity test** (L2): Kourovka 7.19 (printed), and
   `fp-simple-groups-with-arbitrarily-complex-word-problem`.
7. **Out(F_n)** (`fox-rational-section-fails-class-two-virtually`): whether
   H¹(Γ′; H_Q) = 0 for every finite-index Γ′ ≤ Out(F_n). A yes shows that
   Aut(F_n) → Out(F_n) never virtually splits for n ≥ 4, which would kill the
   virtual-section route.
8. **Brin–Thompson rigidity.**
   - `kazhdan-subgroups-of-brin-thompson-groups-are-finite` for n ≥ 2 would answer
     Zaremsky 2.19(a) (printed) negatively.
   - `bs12-embeds-in-brin-thompson-2v`, and the growth gap of L3.
9. **Test groups where every current host dies:**
   - Higman's group;
   - Baumslag–Gersten, now reduced to the height-two BS tower over BS(1,2) edges;
   - the q-difference lamplighter, which is solvable but not quasi-linear;
   - Torelli lower-central quotients;
   - B(2,665);
   - D̃_n, Ẽ_{6,7,8} and F̃_4.
10. **Permanence under products**: `boone-higman-closed-under-finite-direct-products`
    (OPEN).
