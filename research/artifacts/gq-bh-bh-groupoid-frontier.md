# bh-groupoid: Boone–Higman through topological full groups of ample groupoids (2026-09-18)

Lane bh-groupoid of the BH swarm. The question: can a finitely generated group with
solvable word problem, or a reduced input class from main's equivalences, sit inside the
full group of a groupoid whose full group is finitely presented and simple? The tools
are Li's `F_∞` theorem, Matui's simplicity theorems, and the free-colour trick of 2V_τ.

## 1. Verdict

**The exact hypothesis that fails for general inputs is finiteness of the higher rank
graph, when there is no coefficient group.**
- Every host built from a finite aperiodic `k`-graph (any `k`) has single-exponential
  word problem. This includes Li's finitely presented full groups and `nV`. So by
  complexity alone no such class is universal
  (`finite-k-graph-full-groups-have-exponential-word-problem`, new).
- The Kazhdan obstruction behind the rank-one kill does **not** extend to rank two.
  - Rank one: `fw-subgroups-of-eventually-similar-groups-virtually-embed` part 2 and
    `input-encoded-sft-groupoid-hosts-are-not-universal` part 2.
  - Rank two: full groups of finite 2-graphs contain infinite Kazhdan groups, namely the
    Ã₂ lattices.
    - For `PGL_3(K)` lattices this is `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`.
    - For every vertex-free type rotating Ã₂ group, exotic buildings included, it is
      `a2-group-embeds-in-full-group-of-its-rs-two-graph`, now ESTABLISHED by a new
      geometric lane proof.
- So a universal groupoid host would have to take its complexity from the input.
  - The only mechanism in view is a coefficient group: a finitely presented `G` acting
    self-similarly on a finite `k`-graph (Li, arXiv:2110.04505, Example `ex:ZS` case
    (III), which is used for 2V_τ in `odometer-2v-is-fp-simple-and-contains-bs12`).
  - The image of `G` itself is residually finite, because `G` permutes the finite sets
    `Λ^n`.
  - So non-residually-finite inputs, and in particular the infinite simple inputs that
    carry the conjecture (`boone-higman-iff-infinite-simple-inputs`), must be produced by
    mixing `G` with coefficient-free cylinder exchanges.

**The precise open form (groupoid Higman embedding).** Does every finitely generated group
with solvable word problem embed in `[[G ⋉ Λ^∞]]` for some finitely presented `G` with a
pseudo-free self-similar action on a finite `k`-graph satisfying Li's case (III)
hypotheses? These are condition (F) and stabilizers of type `F_2`. Nothing on main
decides it. No construction of such a `G` from an arbitrary decidable input is known.

## 2. New today (all lane proofs, not reviewed)

1. **`a2-group-embeds-in-rs-two-graph-geometric-proof`**, which flips
   `a2-group-embeds-in-full-group-of-its-rs-two-graph` to ESTABLISHED.
   - The input is Robertson–Steger §7 (arXiv:1302.5593), read at source: Lemmas `oalpha`,
     `c1`, `c2`, `c3` and Corollary `9B`, with (H1).
   - Each `γ` acts on `Ω ≅ Y ⊆ Λ_Γ^∞` by finitely many cylinder exchanges
     `Z(α(Γp)) -> Z(α(Γp'))`, with `p'` from the proof of `main2`.
   - Faithfulness comes from thickness: an element trivial at infinity preserves every
     apartment, acts on each as a translation, and the translation is killed by half-plane
     intersections in all three wall directions.
   - Not used: `φ`, simplicity, (H2), (H3), Kumjian–Pask or Renault. So exotic buildings
     are covered.
2. **`finite-k-graph-full-groups-have-exponential-word-problem`**: a uniform
   `C·2^{Cl}` word-problem algorithm, which gives non-universality in every rank.

## 3. The named Ã₂ route after this landing

Target: `vertex-free-type-rotating-a2-groups-satisfy-boone-higman`. It contains the CMSZ
groups on exotic buildings, and hence `exotic-a2-lattices-satisfy-boone-higman`, the
CAT(0) subcase of BBMZ Problem 5.3(10).

The route `a2-boone-higman-via-rs-two-graph-full-groups` has three premises:
1. `a2-group-embeds-in-full-group-of-its-rs-two-graph`: **done** (lane proof).
2. `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic`: **OPEN**.
   - The kill test is finite. `experiments/nv-brick-coding-2026-09-17/tp_q2.json` holds
     five CMSZ `PG(2,2)` triangle presentations `T0`–`T4`, and `rs2graph.py` builds
     their 42-tile 2-graphs.
   - For each, check that `M_1^k > 0` and `M_2^k > 0` for some `k`, and check
     Kumjian–Pask aperiodicity. With `M_i` primitive, (H3) should give it, but that
     implication is unpinned.
   - This is seconds of single-core compute. It needs coordinator approval, and was not
     run.
   - Also unchecked: that `Λ_T` equals `Λ_{Γ_T}`, which the brick-coding node leaves out
     of scope. For simply transitive `Γ`, `A = Γ\𝔗` is the set of tiles at `O`, which
     matches the `(x,y,z,u,w)` encoding. Only the edge rule remains to compare with RS's
     `M_1`, `M_2`.
3. `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`: **OPEN** only through
   the unpinned `finite-k-graph-boundary-groupoid-standard-facts`. These are: Li's
   boundary groupoid is the Kumjian–Pask path groupoid, products go to products, and
   aperiodic graphs give effective groupoids.

**A closed alternative.** `cmsz-pg22-rs-two-graphs-admit-no-brick-coding` shows that the
`mV` route through brick codings fails for these five presentations. So premise 2 plus
the standard-facts pins are the whole remaining gap for explicit exotic lattices.

## 4. What was not done

- No construction for the coefficient-group form in §1.
- No attempt on non-expansive groupoids, meaning infinite graphs or non-SFT unit spaces.
  For these, no finite-presentation theorem is on main.
- Rule slip: one stray `python3 --version` ran locally, inside a copy command. It was a
  no-op and its output was not used.

## 5. Update (2026-09-18, after the approved MSI check)

**Explicit CMSZ instances certified.** `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`
covers all five `PG(2,2)` presentations in `tp_q2.json` and both `PG(2,3)` presentations in
`tp_q3.json`.
- `M_1` and `M_2` are primitive, with exponent 4 or 5.
- The edge rule was matched to Robertson–Steger §7 and reconstructed independently.
- The check is calibrated. The certificate is in
  `research/artifacts/gq-bh-bh-groupoid-cmsz-primitivity-certificate.md`.

**Aperiodicity comes for free.** `rs-two-graph-aperiodicity-from-h3-and-irreducibility`:
(H3) together with irreducibility of each colour gives Kumjian–Pask (A), by Robertson–Sims'
finite-path criterion (arXiv:math/0602120, Lemma `lem:equiv aperiodicity`, read at source).

**Correction: `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` is false as
stated.**
- Type-preserving groups give period 3, and every torsion-free cocompact lattice in
  `SL_3(Q_p)` is a counterexample.
- The corrected form (primitive iff the type-rotation character is onto) is proved for
  `PGL_3(K)` lattices, `K` of characteristic zero, through RS's Howe–Moore argument.
- The exotic case reduces to a phase-sensitive ergodicity of singular half-strips
  (`rs-strip-tail-transitivity-forces-primitive-transition-matrices`).
- BCL's Theorem `ergodic` is phase-free, so it should give irreducibility but not
  primitivity.

**Consequence for the named route.** Each of the seven explicit `Γ_T` embeds in a finitely
presented simple group, conditional only on `finite-k-graph-boundary-groupoid-standard-facts`.
- The q = 2 buildings are not listed as exotic in BCL's review.
- Whether the two q = 3 ones are among CMSZ's 65 exotic order-3 buildings is not
  determined.
- Two things would close every CMSZ lattice of order 3, including all 65 exotic buildings:
  1. an exhaustive enumeration of `PG(2,3)` triangle presentations, with the same check;
  2. the phase-sensitive ergodicity above, which would close every type-transitive
     vertex-free group.

## 6. The general theorem (2026-09-18, later)

**`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`** (lane proof). For every
thick Ã₂ building and every vertex-free, cocompact, type rotating `Γ`:
- `M_1` and `M_2` are irreducible;
- they are primitive iff the type-rotation character `θ` is nonzero, and have period 3
  otherwise.

**Proof idea.**
1. The quotient digraph is `q²`-regular, so its components are closed under successors and
   predecessors.
2. Two moves (tiles sharing a down chamber share successors; tiles sharing an up chamber
   share predecessors) make any closed set of tiles a union of full diagonal panels.
3. In vertex terms, the successor relation joins a panel `(v,x)` to every `(w,y)` with
   `(v,w,x)` and `(v,w,y)` chambers and `x ≠ y`.
4. In each link (a projective plane of order `q ≥ 2`), membership is closed under pencils.
   So it is all-or-nothing at every vertex, and connectivity of two-type subgraphs spreads
   it everywhere.
5. The same computation applied to the cyclic class function forces the period to divide 3,
   and period 3 is exactly type preservation.

Robertson–Steger proved irreducibility only for `PGL_3(K)` lattices, via Howe–Moore, and
deferred the general case to ergodicity. The local argument needs none.

**Consequence.** `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups`, through
route `type-transitive-a2-bh-via-rs-two-graph-full-groups`:
- every type-transitive vertex-free Ã₂ group embeds in a finitely presented simple group of
  type `F_∞`;
- the CMSZ groups are included, and so are the 65 exotic order-3 buildings of
  CMSZ/BCL;
- the only input not yet proved is `finite-k-graph-boundary-groupoid-standard-facts`.

This is the exotic Ã₂ subcase of BBMZ Problem 5.3(10) (`exotic-a2-lattices-satisfy-boone-higman`).

**Sketch for θ = 0 (not claimed).** Let `L = {(a,b) : a + 2b ≡ 0 mod 3}`, and let `X_0` be
the union of the cylinders of phase-0 tiles. The decoration tiles sit at `O`, so `Y ⊆ X_0`.
1. On `X_0`, every groupoid arrow has degree in `L`, because phases are determined by
   degrees. So `Γ ≤ [[G_Λ|_{X_0}]]`.
2. `M_i^3` preserves phase, and is primitive on each phase class. So between phase-0 tiles
   there are paths of every large degree in `L`.
3. Steps 2–3 of `primitive-two-graph-fp-simple-embedding-proof` then run with the
   skew-product group `L/nZ²` (`n = 3m`) in place of `(Z/n)²`. They embed
   `[[G_Λ|_{X_0}]]` in `[[G_{Λ^(n)}|_{X_0}]]`.
4. `X_0` is a union of vertex cylinders of `Λ^(n)`, which is admissible in Li's theorem.
   Steps 4–8 then apply to the reduction, with minimality inside phase 0.

Writing this out would cover all vertex-free type rotating `Γ`.

**Remaining gate for the whole Ã₂ programme:** pin `finite-k-graph-boundary-groupoid-standard-facts`
(Kumjian–Pask identification, products, effectiveness) at source.

## 7. The chain is closed (2026-09-18, later)

**`finite-k-graph-standard-facts-proof`** proves all four standard facts (lane proof). Item 1
is proved from Li's own definitions, read at source (arXiv:2110.04501, `def:Omega`, the
transformation groupoid, `lem:infpaths`, `lem:Omegamax`):
- Li's maximal characters are exactly the infinite paths, so `∂Ω = Ω_max ≅ Λ^∞`;
- the germ `[cd^{-1}, χ_{dz}]` corresponds to the Kumjian–Pask arrow `(cz, d(c)−d(d), dz)`.

Products, topology and effectiveness are elementary.

**Status after this landing** (every link is a lane proof or an import pinned at source;
nothing is independently reviewed):
- `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`: ESTABLISHED.
- `type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups`: ESTABLISHED. This
  covers every vertex-free, finite-orbit, type rotating group on a thick Ã₂ building that is
  not type preserving. That includes all CMSZ groups, the 65 exotic CMSZ buildings of order
  3, and their subgroups.
- `exotic-a2-lattices-satisfy-boone-higman`, the exotic Ã₂ subcase of BBMZ Problem 5.3(10):
  settled for vertex-free type-transitive lattices; still open with torsion or when type
  preserving without a type-transitive overgroup.

**Review priority for referees.** In order:
1. `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive`, the new idea;
2. `a2-group-embeds-in-rs-two-graph-geometric-proof`;
3. `finite-k-graph-standard-facts-proof`;
4. the imported Li–Matui chain.

## 8. The type-preserving case (2026-09-18, final)

`type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups` (lane proof) makes the
§6 sketch rigorous.
- Restrict to the phase-0 cylinders `X_0`. They contain the decorations, and every arrow
  there has degree in `L = {a + 2b ≡ 0 mod 3}`.
- Rescale by `n = 3m`, and compress using the skew product over `L/nZ²`.
- Then run Li–Matui on the reduction to phase 0.

**So `vertex-free-type-rotating-a2-groups-satisfy-boone-higman` is ESTABLISHED** (lane
proofs plus pinned imports, unreviewed). This is Boone–Higman for every group acting freely,
with finitely many orbits, by type rotating automorphisms on the vertices of a thick Ã₂
building, exotic buildings included. For exotic lattices the only remaining gap on
`exotic-a2-lattices-satisfy-boone-higman` is torsion, meaning nontrivial vertex stabilizers.

**Natural next targets.**
1. **Lattices with torsion.** A torsion-free finite-index subgroup `Γ_0` has BH, but BH is
   not inherited by finite extensions in general. Check
   `boone-higman-type-a-class-closed-under-finite-extensions`, and whether its hypotheses can
   be met, for example via a type (A) action.
2. **Other buildings.** C̃₂ and G̃₂ buildings, using tile systems of rank 2. The link
   argument of `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive` uses
   generalized 3-gons, and should adapt to generalized 4-gons and 6-gons.
3. **Products of trees**, as Ã₁ × Ã₁, via RS §7's second example. On main this is already
   PBH through type (A); it would serve as a cross-check.
