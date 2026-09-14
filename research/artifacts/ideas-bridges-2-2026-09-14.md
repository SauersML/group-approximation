# Bridges between famous problems, round 2 (ideas-bridges-2, 2026-09-14)

This lane generated ideas first, killed the weak ones quickly, then proved the
survivor.

**Status labels.**
- **PROVED:** landed as an ESTABLISHED claim, unreviewed.
- **IDEA:** a statement with a kill test and an exact gap; nothing landed.
- **KNOWN / ON MAIN / KILLED:** dropped, with the reason.

**Scope.** Kervaire–Laudenbach (KL); Whitehead / Eilenberg–Ganea (EG) /
Andrews–Curtis (AC); Boone–Higman; Thompson F; Gromov RF / nonsofic hyperbolic
groups; Kaplansky / Atiyah; Gottschalk; fp intermediate growth. Non-hyperlinear
existence is out of scope.

**Read first.** Round 1 is `research/artifacts/ideas-bridges-2026-09-13.md`
(B1–B13, on main at 3d31757e8). Also read: FRONTIER root headings in scope,
`contractible-2-complex-minus-a-cell-is-aspherical`,
`lot-complexes-with-vanishing-first-l2-betti-are-aspherical`,
`acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`,
`andrews-curtis-conjecture`, `stable-andrews-curtis-conjecture`,
`fp-intermediate-growth-witness-exclusions` and
`local-restricted-burnside-iff-lef-burnside-groups-are-finite`.

## 1. Sources read this lane (verbatim pins)

- **S1.** M. A. Cerdeiro, *A class of locally indicable LOT groups* (preprint PDF,
  cms.dm.uba.ar), p. 2:
  - "Howie had proved in [How83] that if a 2-complex L can be 3-deformed to a
    point, and e is a 2-cell of L, then the subcomplex K = L − e can be
    3-deformed to a LOT complex. A consequence of this fact is that if the
    Andrews-Curtis conjecture were true, then the asphericity of LOT complexes
    would imply the compact case of the Whitehead conjecture. Recall that the
    Andrews-Curtis conjecture asserts that every contractible 2-complex can be
    3-deformed to a point (see [AC65])."
  - Same page: "Howie showed in [How85] that LOT complexes are 2-dimensional
    spines of ribbon disc complements."
  - "Remark 1.3. If a LOT group is locally indicable, then the LOT is aspherical."
  - "It is not known whether all LOT groups are LI."
- **S2.** M. A. Cerdeiro, E. G. Minian, *A new approach to Whitehead's asphericity
  question*, arXiv:1203.5348v1, p. 1:
  - "Theorem 1.1 (Howie). If the answer to Whitehead's question is negative, then
    there exists a counterexample K ⊂ L of one of the following two types:
    (a) L is finite and contractible, K = L − e for some 2-cell e of L, and K is
    non-aspherical. (b) L is the union of an infinite chain of finite
    non-aspherical subcomplexes K = K_0 ⊂ K_1 ⊂ ⋯ such that each inclusion map
    K_i → K_{i+1} is nullhomotopic."
  - "In 1996 E. Luft [9] proved that the existence of a counterexample of type (a)
    actually implies the existence of a counterexample of type (b)."
  - "Howie proved that if the Andrews-Curtis conjecture and the ribbon disc
    complements conjecture are true, then there are no counterexamples of type (a)."
- **S3.** A. N. Barreto, E. G. Minian, *Local indicability of groups with homology
  circle presentations*, arXiv:2308.07447v1, p. 2: "Local indicability of LOT
  groups is an open problem (that would imply asphericity of the associated
  presentations). In fact, it is not even known whether all LOT groups are
  torsion-free."
- **S4.** M. Szymik, N. Wahl, *The homology of the Higman–Thompson groups*,
  arXiv:1411.5035, Invent. Math. 216 (2019), abstract: "We prove that Thompson's
  group V is acyclic".
- **S5.** C. Bleak, M. Quick, *The infinite simple group V of Richard J. Thompson:
  presentations by permutations*, arXiv:1511.02123, Groups Geom. Dyn. 11 (2017),
  abstract, as extracted by a web tool: "three generators and eight relations",
  plus a Tietze-derived presentation with two generators and seven relations.
- **Not read at source.**
  - Howie, Topology 22 (1983) 475–485: ScienceDirect refused the web tool with
    HTTP 403 and returned a bot-check page to MSI curl.
  - Ivanov, J. Algebra 216 (1999) 13–19: only a search-engine summary. UNVERIFIED.
  - Ye, J. Algebra 402 (2014): abstract only.

## 2. Ranked bridges

**R1. PROVED: a balanced Kervaire failure refutes stable AC or puts torsion into a LOT group.**
- *Statement:* `balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free`.
  Let `G != 1` be balanced with `G_w = 1`.
  - If `P_w = <X, t | R, W>` is stably AC-trivial, then some LOT group is
    `G * Z`. It has torsion, is neither hyperlinear nor MF, and its LOT complex
    is not aspherical.
  - Conversely, a LOT group `H * Z` with `H != 1` is a killing failure over `H`.
- *Corollary route:* `kervaire-killing-form-via-stable-ac-and-torsion-free-lots`.
  Stable AC together with `lot-groups-are-torsion-free` (OPEN, S3) gives
  `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`. Hyperlinear or
  MF LOT groups, or LOT groups that are never `H * Z`, work as well.
- *Proof:* `balanced-kervaire-stable-ac-lot-proof`.
  1. B1 gives `L` contractible, `pi_2(K) != 0`, and torsion in `G`.
  2. `L - e_W = K v S^1`.
  3. Howie's theorem (`howie-point-deformable-complex-minus-cell-deforms-to-lot`,
     import from S1 and S2) 3-deforms it to a LOT complex, which preserves `pi_1`
     and `pi_2`.
- *Why new here:* main had no LOT, ribbon or 3-deformation claim node; greps found
  only artifacts. Round 1's B5 looked for an AC-invariant in sub-presentations and
  found none. R1 is the working replacement: under stable AC the deleted-cell
  complement is forced into the LOT class.
- *Attack surface:*
  - Torsion-freeness of LOT groups is strictly weaker than LOT asphericity, which is
    what `kervaire-killing-form-via-one-cell-whitehead` needs.
  - Any torsion found in a LOT group refutes the ribbon-disc asphericity conjecture.
  - A proof of torsion-freeness turns stable AC into the balanced killing form.
- *Kill test (passed):* a known theorem making LOT groups torsion-free would reduce
  R1 to a corollary of known results. S3 (2023) says this is open.
- *Caveats:*
  - The primary Howie paper is unread.
  - The realization of (AC1)–(AC5) by 3-deformations is recalled, and sketched in
    the proof node.
  - No novelty is claimed; this is a three-step composition.

**R2. IDEA: Eilenberg–Ganea, stable AC and LOT asphericity cannot all hold?**
- *Statement:* combine `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`
  with Howie (S1, S2).
- *Exact gap:* item 3 of that node puts a finite non-aspherical `K` inside a
  contractible 2-complex `Y` that need not be finite. `H_L` is not finitely
  presented, so a 2-dimensional model is infinite. Howie's AC consequence covers
  only type (a), and by S2 (Luft) type (a) implies type (b), not conversely. So a
  Bestvina–Brady counterexample may be of type (b) only.
- *Kill test:* reread Bestvina–Brady pp. 469–470 (main artifact
  hl-whitehead-bestvina-brady-2026-09-13). Can `Y` be replaced by a finite
  contractible complex minus one cell?
  - If the argument needs the whole infinite level set, R2 dies.
- *Payoff if it survives:* "EG false, or stable AC false, or some ribbon disc
  complement is not aspherical", with no hypothesis.

**R3. IDEA: a balanced presentation of Thompson's V.**
- *Statement:* suppose `V` has a finite presentation with as many relators as
  generators. By item 3 of `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`
  (normal-closure transfer, `V` simple), a killing failure over ANY nontrivial
  subgroup of `V` is a balanced failure over `V`. So:
  - `contractible-2-complex-minus-a-cell-is-aspherical` would give the killing form
    over every nontrivial subgroup of `V`;
  - by R1, stable AC plus torsion-free LOT groups would give the same.
- *Why plausible:* `V` is acyclic (S4), so Epstein's bound allows deficiency 0. The
  known small presentations have deficiency −5 (S5).
- *Kill test:* a certified search for a 2-generator 2-relator or 3-generator
  3-relator presentation of `V`, with Tietze derivations of the dropped relators
  (MSI job, not run). There is no L² obstruction: a balanced complex of an infinite
  group just has `b_2^(2) = 1 + b_1^(2)`.
- *Value:* moderate. It ties `kl-holds-over-thompson-v` (killing form only) to
  Whitehead and AC. The same question for `L_{F_2}(1,2)^x`
  (`leavitt-units-two-generator-fifteen-relator-presentation`) needs `H_2 = 0`
  first, which is unknown here.

**R4. IDEA, folded into R1: free splittings of LOT groups are Kervaire failures.**
- LOT groups have weight one, so `G(Gamma) = H * Z` with `H != 1` is exactly a
  killing failure over `H` (item 2 of R1).
- *Test:* Grushko-type splitting detection for small LOT groups where the word
  problem is solvable, for example the hyperbolic LOT groups of Rosebrock (recalled
  through S1, not read).
- *Kill criterion:* a proof that LOT groups are freely indecomposable. None is known
  to this lane.

**R5. KNOWN: asphericity going up implies Kaplansky zero divisors (Ivanov 1999, unverified).**
- *Summary (search engine):* Ivanov conjectured that asphericity of a presentation
  passes to the presentation with one generator and one relator added, under
  hypotheses. A counterexample gives a torsion-free group whose integral group ring
  has zero divisors. The conjecture holds when the group is locally indicable.
- *Relation to R1:* none. B1 is about a sub-presentation failing asphericity, and
  Ivanov is about the super-presentation. Record only.

**R6. KNOWN: a homotopy description of the unit conjecture (Ye 2014).** Abstract only.
Killed as known literature.

**R7. ON MAIN: nonsofic or non-RF hyperbolic groups from marked limits.**
- `local-approximation-properties-are-marked-closed` and
  `free-burnside-is-a-limit-of-hyperbolic-groups` already carry it.
- *Extra observation (proved in this paragraph):* for finitely presented `G`, a limit
  of subgroups of hyperbolic groups is fully residually such subgroups. So for fp
  inputs the route is a residual property.
- `BS(2,3) = <a, t | t a^2 t^-1 = a^3>` is not residually hyperbolic.
  1. In a hyperbolic quotient, `a` has finite order, since the translation length
     would satisfy `2 tau = 3 tau`. Call the order `N`.
  2. `a^2` and `a^3` are conjugate, so they have the same order, which forces
     `gcd(N,6) = 1`.
  3. Then `<a^2> = <a> = <a^3>`, so `t` normalizes `<a>`.
  4. So `[t a t^-1, a] != 1` (Britton) dies in every hyperbolic quotient.
- So fp non-RF groups of Baumslag–Solitar type cannot feed the residually-hyperbolic
  route to `non-residually-finite-hyperbolic-group`.

**R8. TRIVIAL: a killing failure over a hyperbolic group gives a non-RF nonsofic hyperbolic group.**
This is round-1 B8. A failing group has no nontrivial finite quotient, and is not
hyperlinear, by Gerstenhaber–Rothaus and Pestov. Killed.

**R9. KNOWN: Gottschalk localizes to finite balls.**
- Injectivity of a CA is witnessed on a finite ball (compactness), and so is a
  Garden-of-Eden pattern. So nonsurjunctivity is open, and surjunctive marked
  groups form a closed set.
- So Gottschalk's conjecture holds iff it holds for finitely presented groups.
- Recalled as standard (Ceccherini-Silberstein–Coornaert), not pinned. Killed as
  known; main has the fg-simple reduction.

**R10. KNOWN: killing failures pass to every nontrivial quotient.** So the killing form
over `G` follows from Kervaire–Laudenbach over any nontrivial quotient of `G`.
Standard. Killed.

**R11. TRIVIAL: Gromov RF implies the killing form over every hyperbolic group.** Use a
nontrivial finite quotient and Gerstenhaber–Rothaus. Killed.

**R12. CONSTRAINT, not a bridge: an fp group of intermediate growth has deficiency ≤ 0.**
1. Infinite amenable groups have `b_1^(2) = 0`, so a presentation complex `K` has
   `b_2^(2)(K) = 1 - def >= 0`.
2. If `def = 1`, `K` is aspherical (`finite-2-complex-with-zero-second-l2-betti-is-aspherical`)
   with `chi = 0`, so `b_1 >= 1` and `G` maps onto `Z`.
3. With no free subgroups, Bieri–Strebel makes `G` an ascending HNN extension of a
   finitely generated base.
   - If strictly ascending, there is a free subsemigroup, hence exponential growth.
   - Otherwise `G = B x| Z` with `B` finitely generated and normal of infinite index
     in a group of cohomological dimension 2. So `B` is free (Bieri), and the growth
     is exponential or polynomial.
- Bieri–Strebel and Bieri were recalled, not pinned. Likely known (Hillman). It
  overlaps item 4 of `fp-intermediate-growth-witness-exclusions`. Handed to growth
  lanes; not landed.

**R13. KILLED (round-1 B12 again): Kervaire failure gives nonsurjunctivity.** There is
still no mechanism turning a killing word into a cellular automaton.

**R14. KILLED (round-1 B5): AC-invariants of sub-presentations.** AC moves mix all
relators, so no sub-presentation survives. R1 is the replacement.

**R15. KILLED: Thompson F against KL, Whitehead or AC.**
- F is torsion-free, so Klyachko settles KL over it.
- F has type F∞ and contains `Z^n` for every `n`, so it carries no 2-complex input.
- Its amenability is equivalent to known Ore and Myhill-type statements; no new
  bridge.

**R16. KILLED (round-1 B13): Eilenberg–Ganea against strong Atiyah on Bestvina–Brady kernels.**
`H_L` is not finitely presented, so no finite 2-dimensional model and no L²-Euler
characteristic constraint.

## 3. Landed

- `balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free` (ESTABLISHED)
- `balanced-kervaire-stable-ac-lot-proof` (route)
- `howie-point-deformable-complex-minus-cell-deforms-to-lot` (ESTABLISHED, literature
  import)
- `howie-3-deformation-lot-citation` (route)
- `lot-groups-are-torsion-free` (OPEN)
- `kervaire-killing-form-via-stable-ac-and-torsion-free-lots` (route into
  `kervaire-killing-form-holds-over-nonnegative-deficiency-groups`)

## 4. Exact gaps

- **G1.** Read Howie, Topology 22 (1983), at source, and confirm the 3-deformation
  statement and its hypotheses (finiteness of `L`, arbitrary `e`).
- **G2.** R2: is some Bestvina–Brady Whitehead counterexample of type (a)?
- **G3.** R3: does `V` have deficiency 0?
- **G4.** The input R1 needs: are LOT groups torsion-free? Or, cheaper, is some small
  LOT group a free product `H * Z`?

## 5. Best next deep lane

**hl-lot-torsion.** Decide torsion-freeness of LOT groups, or certify torsion in one.
- Through R1, a proof plus stable AC gives the balanced Kervaire killing form.
- Torsion found in a LOT group refutes asphericity of ribbon disc complements, a
  well-known test case of Whitehead's conjecture.
- Handles:
  - Barreto–Minian's concatenable minima (their Theorems 2.5 and 2.9, S3) and
    Howie's `I`/`T` graphs, to push local indicability to more LOTs;
  - a census of small LOTs on MSI, certifying torsion candidates by a derivation of
    `g^k = 1` plus a finite quotient separating `g` from 1.
