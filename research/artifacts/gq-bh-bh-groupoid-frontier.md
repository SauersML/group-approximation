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
