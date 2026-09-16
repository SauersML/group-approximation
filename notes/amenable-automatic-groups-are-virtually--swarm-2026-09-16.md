# Amenable automatic groups are virtually abelian: swarm attack, 2026-09-16

- **Lane:** `swarm-amenable-automatic-groups-are-`.
- **Hole locked and worked:** `amenable-automatic-groups-are-virtually-abelian` (H).
- **Full proofs:** `research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`.
- **Scripts:** none. Nothing in this lane is computational.
- **Outcome:** a reduction. The hole is still open. It is now equivalent, modulo five
  imported theorems, to the conjunction of Thurston's conjecture (S) and the
  elementary-amenability statement (EA). Separately, a growth dichotomy for all automatic
  groups is proved.

## Setup

(H) says that an amenable group with an automatic structure (Epstein–Cannon–Holt–Levy–
Paterson–Thurston, *Word Processing in Groups*, 1992; abbreviated ECHLPT) has an abelian
subgroup of finite index. Inside this graph it gives:

- `thompson-f-is-not-both-amenable-and-automatic`;
- `thompson-f-not-automatic-via-amenable-rigidity`, together with `thompson-f-is-amenable`;
- a yes answer to Zaremsky Problem 4.1, through
  `amenable-automatic-rips-via-virtually-abelian`.

Before this lane its Attempts recorded the nilpotent case, the metabelian test cases
`BS(1,n)` and `Z ≀ Z`, and the observation that the Dehn function cannot suffice
(higher Heisenberg groups).

## Status gate (checked 2026-09-16)

- **Rees**, *The development of the theory of automatic groups* (arXiv:2205.14911v1,
  30 May 2022), was read on 2026-09-16.
  - p. 14 (PDF page): "It was conjectured by Thurston that the same result must hold for
    an automatic soluble group. That conjecture remains open, but it was proved for
    automatic polycylic groups in [39]" (Harkins, PhD thesis, Newcastle, 2001), "Much
    more recently it was proved in [69] that biautomatic soluble groups must be
    virtually abelian."
  - p. 27 lists "whether all soluble automatic groups must be virtually abelian" among
    the open questions, with Romankov [69] as "the most recent progress".
- **Romankov**, arXiv:1511.00223v1 (1 November 2015), Theorem 6.3, read 2026-09-16:
  finitely generated soluble biautomatic groups are virtually abelian.
- **arXiv API searches**, 2026-09-16, math.GR, title and abstract fields only:
  - `abs:"automatic" AND abs:"soluble"`: 1 hit;
  - `abs:"automatic" AND abs:"solvable"`: 11 hits;
  - `abs:"automatic group"`: 39 hits;
  - `abs:"automatic" AND abs:"amenable"`: 5 hits;
  - `abs:"automatic structure" AND abs:"growth"`: 5 hits.
  - The 2024–2026 hits and their titles are:
    - arXiv:2405.17695v1 (27 May 2024), *The Limit Space of Self-similar Groups and
      Schreier graphs*;
    - arXiv:2508.01075v1 (1 August 2025), *Cyclic orders and actions of Leary--Minasyan
      groups on coarse PD(n) spaces*;
    - arXiv:2607.26284v1 (28 July 2026), *Stallings foldings for rational subsets of
      automatic groups*;
    - arXiv:2606.24287v1 (23 June 2026), on Lie skew braces.
  - None of them concerns soluble or amenable automatic groups.
  - No statement of (H) or (S), proved or refuted, was found. The WebSearch budget ran
    out earlier in the session, so no general web search beyond arXiv was done. The
    status is "open" as far as a bounded arXiv check can tell.
- **Unread hits:**
  - arXiv:1711.01256, *Weighted growth functions of automatic groups*, listing only;
  - arXiv:1312.3710, about automatic graphs, a different notion.

## What was proven

### 1. The growth dichotomy (artifact Sections 1–5)

**Theorem 4.** Every automatic group is virtually abelian or contains a free
subsemigroup of rank 2.

Graph nodes:
- claim `automatic-groups-virtually-abelian-or-free-subsemigroup`;
- route `automatic-va-or-free-subsemigroup-proof`.

The proof has four steps.

- **Lemma 1.** With an automatic structure with uniqueness, the representative `w_g`
  satisfies `|w_g| <= S|g| + |w_1|`, where `S` bounds the states of the multiplier
  automata.
  - If `|w_{ga}| > |w_g| + S`, the run on the padded pair repeats a state in the tail
    where the first coordinate is `$`.
  - Pumping that loop down gives a strictly shorter word of `L` for the same element,
    which contradicts uniqueness.
  - The argument works because deleting tail letters keeps the pair padded and its
    first coordinate unchanged.
- **Lemma 3.** For a trim DFA of `L`, exactly one of the following holds.
  - Some state has two distinct first-return loops. They form a prefix code, so they
    generate a free submonoid of `A*` inside the loop set.
  - Every nontrivial strongly connected component is a single cycle, and `L` has
    polynomial growth.
- **Loop case.** Uniqueness transports the free submonoid of loops to `G`, through the
  injectivity of `α ↦ λ(x φ(α) z)` followed by cancellation.
- **Polynomial case.** `G` has polynomial growth by Corollary 2. So `G` is virtually
  nilpotent (Gromov). A nilpotent finite-index subgroup is automatic, hence virtually
  abelian (ECHLPT).

**Corollary 5.** An automatic group of subexponential growth is virtually abelian.

**Novelty.** None is claimed; see artifact Section 5.
- Rees p. 14 describes the ECHLPT nilpotent proof as using "the fact that a regular
  language with polynomial growth cannot satisfy a (synchronous) fellow traveller
  property", which is the same circle of ideas.
- The free-subsemigroup form was not found stated in the sources read.
- A referee should treat Theorem 4 as folklore-level.

**What Theorem 4 does not give.** It does not reach (H): every finitely generated
soluble group that is not virtually nilpotent already contains a free subsemigroup of
rank 2 (Rosenblatt; Chou; from memory). The example `BS(1,2)` is in artifact
Section 4.

### 2. The equivalence (artifact Section 6)

- (S) = `soluble-automatic-groups-are-virtually-abelian`, open.
- (EA) = `amenable-automatic-groups-are-elementary-amenable`, open.

**Proposition 6.** (H) ⟺ (S) ∧ (EA), given three imports:
- (Fin) automatic groups are of type `F_∞`;
- (KMN) elementary amenable groups of type `FP_∞` are virtually soluble;
- (FI) finite-index subgroups of automatic groups are automatic.

Routes:
- `amenable-automatic-va-via-ea-and-soluble-case`: (S) ∧ (EA) ∧ imports ⇒ (H);
- `soluble-automatic-va-from-amenable-case`: (H) ⇒ (S);
- `amenable-automatic-ea-from-virtually-abelian-case`: (H) ⇒ (EA).

**Proposition 7.** `every-f-infinity-amenable-group-is-elementary-amenable` ∧ (Fin) ⇒
(EA). Route: `amenable-automatic-ea-via-f-infinity-amenable-ea`. So (EA) sits under the
nonexistence answer to Zaremsky Problem 1.12.

### 3. The soluble half is exactly polycyclicity (artifact Section 7)

- (P) = `soluble-automatic-groups-are-polycyclic`, open.
- Given Harkins' theorem (`polycyclic-automatic-groups-are-virtually-abelian`), (S) ⟺ (P).
  - (P) ⇒ (S): route `soluble-automatic-va-via-polycyclic-case`.
  - (S) ⇒ (P): route `soluble-automatic-polycyclic-from-virtually-abelian-case`.
- By Mal'cev's theorem as quoted by Romankov, (P) says that every abelian subgroup of a
  soluble automatic group is finitely generated.

### 4. New imports (secondary citations; each is a claim plus a `requires: []` route)

| claim | route | source actually read |
| --- | --- | --- |
| `automatic-groups-admit-structures-with-uniqueness` | `automatic-structures-with-uniqueness-citation` | Engel–Wulff arXiv:1711.06836v3 §3.6 p. 28; Rees p. 9 |
| `finite-index-subgroups-of-automatic-groups-are-automatic` | `finite-index-automatic-subgroups-citation` | Rees p. 13 |
| `automatic-nilpotent-groups-are-virtually-abelian` | `automatic-nilpotent-groups-are-virtually-abelian-citation` | Rees p. 14 |
| `automatic-groups-are-of-type-f-infinity` | `automatic-groups-are-of-type-f-infinity-citation` | Brittenham–Hermiller–Johnson arXiv:1506.00071v1 p. 3; Engel–Wulff pp. 28, 50; Rees Prop. 2.1; Zaremsky remark as recorded in the graph |
| `elementary-amenable-fp-infinity-groups-virtually-soluble` | `ea-fp-infinity-virtually-soluble-citation` | St. John-Green, arXiv:1410.4363v1 (thesis), §6.2.7, PDF p. 133, citing [KMPN09, p. 4] |
| `polycyclic-automatic-groups-are-virtually-abelian` | `polycyclic-automatic-groups-virtually-abelian-citation` | Rees p. 14 citing Harkins [39] |

None of ECHLPT, Alonso, Kropholler–Martínez-Pérez–Nucinkis or Harkins was read in the
primary source. The trust surface is those four primary sources as reported by the
secondary sources above.

## Approaches and where they die

### A. Running Romankov's biautomatic proof for automatic groups (artifact Section 7)

Romankov's proof of Theorem 6.3 was checked step by step with "biautomatic" replaced by
"automatic".

- **Steps that survive.**
  - R1: type `FP_∞`, by (Fin).
  - R2: finite vcd (Kropholler, as quoted by Romankov).
  - R3: finite rank and minimax (Kargapolov, Robinson–Zaĭcev, as quoted).
  - Conclusion: a counterexample to (S) contains a finite-index subgroup `H` that is
    torsion-free, automatic, soluble minimax and nilpotent-by-(virtually abelian).
- **Steps that die.**
  - R4 needs Gersten–Short to exclude `UT_3(Z)` as a subgroup.
  - R5 needs the minimal condition on centralizers, which yields the maximal condition
    on abelian subgroups.
  - Both are biautomatic-only tools. This lane knows no substitute for automatic groups.
- **Side finding.** In R4, Romankov writes `[u, y] ∈ ζ_1(H)` where the argument gives
  `ζ_1(N)`. The argument needs only `ζ_1(N)`, so nothing breaks. The correction is in
  the artifact.
- **Consequence.** Once `H` is polycyclic, Harkins replaces R6 and R4 becomes
  unnecessary. The only missing input is (P).

### B. Dehn function

Automatic groups have quadratic Dehn function, and that already kills the model case
`BS(1,n)`: its Dehn function is exponential (Rees pp. 11–12). But it does not reach (P).
De Cornulier–Tessera (arXiv:1003.0148, abstract read 2026-09-16) embed `BS(1,n)` in
finitely presented metabelian groups with quadratic Dehn function. The PDF fetch failed
three times with a connection reset, on 2026-09-16, so the examples were not
identified.

### C. Growth

Theorem 4 is sharp for what growth can say. A counterexample to (H), (S) or (EA) grows
exponentially, and so does every soluble group that is not virtually nilpotent
(Milnor–Wolf). Growth cannot separate the classes.

### D. Distortion

A counterexample to (P) contains a non-finitely-generated abelian minimax subgroup. In
the metabelian model cases this forces exponentially distorted cyclic subgroups.
Undistorted cyclic subgroups are known to this lane only for biautomatic groups
(Gersten–Short, from memory). Whether cyclic subgroups of automatic groups can be
distorted is not known to this lane.

### E. (EA)

There is no mechanism. It is the automatic case of Zaremsky 1.12, which is open. The
test case is Thompson's `F`: it is `F_∞` and not EA, so (EA) implies that `F` is not
both amenable and automatic. No route records that, because the graph has no verified
node "`F` is not elementary amenable".

### F. A concrete test case for (P), recorded for future lanes

Let

    G_{2,3} = Z[1/6] ⋊ Z^2 = ⟨ a, s, t | s a s^{-1} = a^2,  t a t^{-1} = a^3,  [s, t] = 1 ⟩,

with `(m, n) ∈ Z^2` acting on `Z[1/6]` by multiplication by `2^m 3^n`.

Checked in this lane:

- **Presentation.** `B = BS(1,2) = ⟨a, s | s a s^{-1} = a^2⟩ ≅ Z[1/2] ⋊ Z`. The map
  `φ : a ↦ a^3, s ↦ s` preserves the relation, since `s a^3 s^{-1} = a^6 = (a^3)^2`. It
  is injective, being multiplication by 3 on `Z[1/2]` and the identity on the quotient
  `Z`. The ascending HNN extension `B *_φ` has exactly the presentation above. The normal closure of `B` in `B *_φ` is
  `⋃_k t^{-k} B t^k`. Since `t^{-k} a t^k` represents `1/3^k ∈ Z[1/6]`, that union is
  `Z[1/6] ⋊ ⟨s⟩`, so `B *_φ ≅ Z[1/6] ⋊ Z^2`.
- **Type F.** `B` has a finite 2-dimensional `K(B,1)` (the presentation complex of a
  torsion-free one-relator group, from memory: Lyndon). The mapping torus of a cellular
  map realising the injective `φ` is a finite `K(G,1)`. So `G_{2,3}` is of type `F`, and
  in particular of type `FP_∞` with finite cohomological dimension.
- **Consequences.** `G_{2,3}` is soluble and amenable. It is not polycyclic, since
  `Z[1/6]` is a non-finitely-generated abelian subgroup. Hence it is not virtually
  abelian.

So `G_{2,3}` passes every necessary condition this lane can derive: R1–R3, type `F_∞`
and exponential growth. If it were automatic, it would refute (P), (S) and (H) together.
Whether it is automatic is not decided in any source this lane read.

Two ideas, both from memory and unverified:

- **Dehn function.** Groups of this shape may be among the higher-rank "Sol-like"
  S-arithmetic groups with quadratic Dehn function. If so, the Dehn function
  cannot exclude them.
- **Higher-dimensional fillings.** Harkins handled polycyclic groups through ECHLPT
  Theorem 10.3.5. By Rees p. 12 that theorem concerns groups acting properly and
  cocompactly on a k-connected Riemannian manifold. `G_{2,3}` acts on a horocyclic
  product of `H^2` with two trees, which is not a manifold, so 10.3.5 does not apply as
  stated. A proof that `G_{2,3}` is not automatic would plausibly need two inputs:
  - a combing bound on 2-dimensional filling functions for automatic groups of type
    `F`;
  - an exponential lower bound for the 2-dimensional filling of `G_{2,3}`, in the style
    of Young's filling invariants for Sol-type lattices.

  Neither input was fetched or checked. This is a direction, not a result.

## Literature consulted (all accessed 2026-09-16)

**Read (PDF text extracted locally):**
- S. Rees, arXiv:2205.14911v1 (30 May 2022): pp. 9, 11–14, 27.
- V. A. Roman'kov, arXiv:1511.00223v1 (1 November 2015): §§5–6, Theorem 6.3 and its proof.
- A. Engel, C. Wulff, arXiv:1711.06836v3: §3.6, pp. 28 and 50.
- C. Brittenham, S. Hermiller, T. Johnson, arXiv:1506.00071v1: p. 3.
- S. St. John-Green, PhD thesis, arXiv:1410.4363v1: §6.2.7, PDF p. 133.
- M. Fluch, arXiv:1009.4633v2: downloaded and grepped, nothing used.

**Abstract page only:**
- Y. de Cornulier, R. Tessera, arXiv:1003.0148.

**arXiv API listings:** the queries in the status gate.

**Not read; cited only through the secondary sources above, or from memory:**
- ECHLPT, *Word Processing in Groups* (1992): Theorems 2.5.1 and 10.3.5, the nilpotent
  theorem, finite-index inheritance.
- J. Alonso, *Combings of groups* (1992).
- Kropholler–Martínez-Pérez–Nucinkis, J. Reine Angew. Math. 637 (2009).
- A. Harkins, PhD thesis, Newcastle (2001).
- Gersten–Short on biautomatic groups.
- P. H. Kropholler on soluble groups of type `FP_∞`.
- Chou (1980) and Rosenblatt (1974) on free subsemigroups in elementary amenable groups.
- R. Young on filling invariants of solvable groups.
- Lyndon on one-relator groups.

**Growth-related listings not read:** arXiv:1711.01256 and arXiv:1312.3710.

## For a referee

- **Weakest imports.**
  - `polycyclic-automatic-groups-are-virtually-abelian` rests on Rees's one-sentence
    report of an unread thesis.
  - `elementary-amenable-fp-infinity-groups-virtually-soluble` rests on St. John-Green's
    citation of KMPN09.
  - `automatic-nilpotent-groups-are-virtually-abelian` rests on Rees's report of
    ECHLPT.
  - `automatic-groups-are-of-type-f-infinity` rests on Alonso as cited by three
    sources.
- **Weakest proofs.**
  - Lemma 3 of the artifact: the trim-DFA dichotomy and the polynomial growth bound in
    the single-cycle case.
  - Lemma 1 of the artifact: that pumping in the `($, x)` tail preserves membership in
    `M_a`.
  Both are elementary automata theory, written out in full in the artifact.
- **Cycles.** The equivalence routes deliberately create cycles, (H) ⇄ (S) and (H) ⇄
  (EA), as well as (S) ⇄ (P). They record equivalences. The least fixpoint does not let
  them self-justify.
