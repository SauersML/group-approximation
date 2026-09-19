# Boone–Higman: master route (synthesis v1, 2026-09-18)

This is the lead synthesis of the 09-18 BH swarm, written by lane `bh-synth-lead`. It was
written from `gq-bh-bh-writeup-state.md`, from `board/LESSONS.md` (38 lines at 10:58 CDT),
and from the route and obstruction nodes cited below, read on origin/main.

Scope and caveats:
- It is a strategy document, not a proof, and it asserts no new theorem.
- Most nodes it cites are unreviewed lane proofs; their status lines govern.
- The sibling synthesis lanes (hosts, obstructions, reductions) had not posted when v1
  was written. §8 is reserved for merging them.

## 0. Thesis in one paragraph

Almost every obstruction found this week is the same obstruction, and almost every
success is the same success.

- **Why constructions fail.** A finite presentation can only see finitely many local
  configurations. A host is finitely presented only if its global combinatorial
  structure is pinned down by finitely many local rules, with no independent far-away
  perturbation. Call this the **local rigidity principle (LRP)**.
- **Why constructions succeed.** Each successful host is a *rigid finite-type coding* of
  its input: a Li degree category with unique factorization, a finite-nucleus RSG, a
  building whose links force the global structure, or a self-similar tree-pair calculus.
- **Where decidability comes in.** Jeandel's theorem ties decidability to exactly this
  kind of object: a finitely presented group carrying a strongly aperiodic SFT has
  solvable word problem.

**The master route.** Embed each decidable group G in a finitely presented group Λ
carrying an **effective, finite-type, locally rigid Cantor coding**. Then take the
Cuntz-stabilized full group. Comparison, type (A), simplicity and the embedding into a
finitely presented simple group are already proved. So the whole of Boone–Higman, in its
strong permutational form, is concentrated in one object: **rigid aperiodic tilings of
decidable groups**.

## 1. The local rigidity principle: evidence from today's nodes

Every obstruction row below is a *non-rigid model*. Each is a second solution of the
finitely many local rules, invisible to short relators. Every success row is a
*uniqueness mechanism*.

| Kind | Node | The non-rigidity or rigidity mechanism |
|---|---|---|
| kill | `free-shift-houghton-like-envelopes-are-not-fp` | a generic enumeration is locally stable, so far-away transplants are invisible |
| kill | `fsym-containing-fp-groups-are-pinned-by-finitely-many-equations` | Schreier-ball test: a second enumeration with the same L-balls means not fp |
| kill | `houghton-like-envelope-fp-pins-the-enumeration-by-near-relators` | fp forces ν to be the unique solution of finitely many local rules |
| kill | `fp-pl-groups-with-f-have-no-transcendental-support-endpoints` | deformation: relators see finitely many inequalities, so perturb the parameter |
| kill | `fp-alternating-full-groups-of-free-subshifts-force-sft` | fp forces finite type, i.e. finitely many local rules |
| kill | `v-times-golden-silver-wang-product-full-group-is-not-fp` | two independent faults can be translated apart (the difference set splits) |
| kill | `fp-v-times-subshift-full-groups-force-quantum-rigidity` | every operator-valued model of the local rules must commute |
| kill | `annular-free-product-germ-hosts-are-not-finitely-presented` | independent finite quotients per depth; no rule carries depth n to depth n+1 |
| kill | `block-power-germ-schedules-with-fp-germ-group-are-exponential` | fp germ group forces a linear recurrence, so schedules are rigidly bounded |
| kill | `eventually-periodic-genuine-shell-actions-give-fp-envelopes` | in dimension one, the only rigid structures are periodic, so the inputs are virtually abelian |
| success | `finitely-coded-cantor-actions-give-type-a-hosts` | Li's (UFP\*): unique factorization of degrees, so Li's F_n theorem applies |
| success | `a2-lattices-embed-in-fp-simple-groups` | projective-plane links force the tile graph to be irreducible (local to global) |
| success | `cocompact-tree-product-lattices-lie-in-type-a-class` | a cube k-graph, with power and phase to force loops |
| success | `hyperbolic-groups-lie-in-the-permutational-class` | a finite nucleus: the horofunction boundary is a finite-state coding |
| success | `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` | ring side: quantum rigidity suffices for finite presentation |

**Corollaries of the LRP.** These are design rules for every lane.
1. **Dimension one is too small.** N-indexed codings of one-ended groups (Houghton-like
   routes, shells) cannot be both rigid and aperiodic. Rigid means periodic in dimension
   one, which leaves only virtually abelian inputs. Λ-indexed codings of a one-ended Λ
   can be both, because Robinson and Mozes tilings exist. Cohen's theorem (strongly
   aperiodic SFTs need one end) is the matching necessary condition. **The Houghton and
   shell failures are one-dimensional shadows of the tiling route.**
2. **Products create independent faults.** Two uncoupled codings on the factors of
   Λ₁ × Λ₂ give non-rigid models (golden–silver). Simulation designs of the form
   "input constant along Z²-planes" must couple their hierarchy across all directions.
3. **Invariant measures block the known fp mechanisms.** Every recorded
   finite-presentation theorem runs through compression, i.e. pure infiniteness, or
   through a group law. A full-support invariant measure, which exists for every
   free Z²-SFT, excludes compression on the crossed-product side. **Prefer non-amenable Λ**
   (Λ₀ × F₂, or Λ₀ × a hyperbolic group), where free minimal subshifts can be
   paradoxical (`f2-groups-have-paradoxical-free-minimal-subshifts`). Stabilizing by the
   Cuntz groupoid supplies compression on the group side in any case.
4. **Complexity lives in the units or the acting group.** Finite unit groups cap the word
   problem at exponential time (`finite-k-graph-full-groups-have-exponential-word-problem`,
   `complexity-bounded-host-classes-are-not-universal`). A universal host must contain
   the input's own finitely presented envelope Λ as a genuine acting group, as the SFT
   route does, not as germs of V.
5. **Kazhdan inputs.** They cannot pass through V-germ hosts
   (`normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups`). They can pass
   through Λ-acting hosts, because Λ ≤ F(T) is a global inclusion.
6. **Central extensions** whose class survives on point stabilizers cannot be coded over
   a boundary (`central-extension-untwisting-over-boundaries`). So Deligne-type inputs
   need a free coding of their own. The route below provides one: free SFTs are free.
7. **Masses must not be self-similar in a single ratio.** Hosts for Q-divisible inputs
   (GL_n(Q)) need infinitely many independent scaling ratios
   (`no-free-q-odd-action-by-v-has-a-doubling-intertwiner`, lesson). Over a
   Λ-coding that contains GL_n(Q) inside Λ this constraint is vacuous, because the
   divisibility sits in Λ, not in the dynamics.

## 2. Strategy 1 (master route): rigid aperiodic tilings of decidable envelopes

**The chain.** It is already on main as two routes, which share one open core:
`boone-higman-via-v-times-aperiodic-sft-full-groups` (group side) and
`boone-higman-via-leavitt-units-of-rigid-sft-overgroups` (ring side).

```
G decidable
 └─(G0: Clapham)→ Λ₀ ⊇ G, finitely presented, solvable WP        [supplied]
    └─(G1: existence)→ Λ = Λ₀ × H and a free minimal SFT X ⊆ A^Λ   [OPEN]
       └─(G2: rigidity)→ X quantum rigid (at every large D, over F_2)  [OPEN; the crux]
          ├─ ring side:  B = LC(X,F_2) ⋊ Λ is fp (established given G2)
          │               └─(G3r: K)→ K_1 = K_2 = 0 for B ⊗ L_{F_2}(1,2)  [OPEN]
          │                    └─(G4r)→ (B⊗L)^× fp simple ⊇ G   [conditional on Khanh import]
          └─ group side: (G3g: P2′) quantum rigid ⇒ A(G_V × (Λ⋉X)) fp   [OPEN]
                          └─(G4g)→ simple, type (A) ⇒ PBH for G   [supplied]
```

**G0 (supplied).** `clapham-fp-embedding-preserves-word-problem`. By
`boone-higman-iff-simple-kazhdan-decidable-inputs`, G may be assumed simple, Kazhdan,
FA and decidable. The first hard concrete input is Λ₀ = St₁₀(R_L). It is finitely
presented with solvable word problem, both refereed (`leavitt-resolvent-k2-stability-holds`),
quasisimple, and contains every GL_n(Q).

**G1, existence: a free minimal SFT on Λ = Λ₀ × H.**
- *Supplied:*
  - Jeandel: the decidability hypothesis is necessary, so this gate consumes it.
  - Cohen: one-endedness is necessary; any product with an infinite H is one-ended.
  - Barbieri–Sablik–Salo: strongly aperiodic SFTs on products (context only; must be
    read at source).
  - Durand–Romashchenko: minimality for Z^d.
  - `plane-constant-minimal-sft-factors-are-effective-minimal`.
  - The (M1)/(M2) split in `minimal-free-sft-via-plane-constant-minimal-simulation`.
- *Missing:*
  - (M2) an effectively closed minimal free subshift on Λ₀, for any non-abelian simple
    Kazhdan envelope;
  - (M1) a minimal SFT simulation beyond Z^d.
- *Transferable tools:*
  - decidable language from minimality plus effectivity;
  - hierarchical (Robinson or Mozes) layers;
  - `f2-groups-have-paradoxical-free-minimal-subshifts`.

**G2, rigidity (THE crux).** It is necessary for the group side and sufficient for the
ring side.
- *Supplied:*
  - quantum rigidity is equivalent to finite presentation of the Z² crossed product
    (`sft-crossed-product-fp-iff-quantum-rigid`), and sufficiency holds over every
    finitely presented Λ;
  - wall rigidity (first-order rigidity) is equivalent to an idempotent commutator ideal;
  - Labbé's shift is wall-rigid (`labbe-shift-is-wall-rigid`);
  - permutive-triangle SFTs are rigid;
  - periodic quantum tilings refute rigidity, and positive entropy kills it;
  - the golden–silver design warning.
- *Missing:* **no free minimal SFT over any group is yet known to be quantum rigid**,
  not even over Z² (`free-minimal-z2-sft-is-quantum-rigid`). The local-to-global step
  (`wall-rigid-z2-sft-is-quantum-rigid`) is open.
- *Transferable tools:*
  - the Ã₂ link argument, a genuine local-to-global mechanism: pencil closure in
    projective-plane links spreads a property from one tile to all tiles;
  - Li's (UFP\*): unique factorization is rigidity;
  - the crossing-fault network of Labbé's Markov partition.

**G3r, K-theory (ring side).** K₁ = K₂ = 0 for the Leavitt tensor of a free crossed
product (`free-action-leavitt-tensor-hosts-have-trivial-k1-k2`).
- *Supplied:*
  - the gq Leavitt toolkit: unstable K-theory equals stable, one-step stabilization,
    and a refereed K₂ stability chain;
  - the Ara–Brustenga–Cortiñas sequence;
  - working over F₂ avoids the rational-scalar obstruction
    (`leavitt-scalar-commutators-block-fp-central-quotients` kills only Q ⊆ Z(R)).
- *Missing:* control of the K-theory of B ⊗ L for non-regular B. Homotopy K-theory
  vanishes, so the nil-terms are the issue. Also, the Khanh finite-presentation import
  must be read at source.

**G3g, P2′ (group side).** "Quantum rigid ⇒ A(G_V × (Λ ⋉ X)) is finitely presented" is
the converse of the proved necessity theorem. Nobody has attempted it.
- *Tool:* a Stein–Farley complex whose vertices are prefix-tree × pattern-cylinder
  partitions, with Brown's criterion.
- *Where rigidity should enter:* the descending links are joins of "mergeable pattern"
  complexes. Rigidity (unique local extensions) should be what makes them highly
  connected, as UFP\* does in Li's proof.
- *Payoff:* a positive P2′ gives **PBH**, not just BH, through
  `fp-v-times-minimal-action-full-groups-have-type-a-actions`.

**G4 (supplied).**
- Nekrashevych's simplicity of A(T) for minimal T.
- `v-times-ample-full-groups-are-generated-by-transpositions`.
- Type (A) from finite presentation.
- `central-simple-leavitt-tensor-unit-groups-are-simple`.

## 3. Strategy 1b: rigid codings in Li's form (finiteness supplied, coding missing)

`finitely-coded-cantor-actions-give-type-a-hosts` and Li's Theorem `thm:ZS` together
make finite presentation *automatic*. It holds for a finite-object left cancellative
category with degree map, (UFP\*), condition (F), two loops of every colour, and unit
groups of type F_n. So:

> G ∈ B_A whenever some finitely presented Λ ⊇ G acts faithfully by global bisections
> of such a finitely coded, connected-in-pieces groupoid, with finitely presented unit
> groups.

- **What already fits.** Hyperbolic groups, tree-product lattices, Ã₂ lattices, CT_P(Z),
  RCWA groups and 2V_τ are all instances.
- **What is missing.** A coding with *complex units*, since finite units cap the word
  problem at exponential time, that is also *effective* on the boundary. One object with
  unit group Λ is a self-similar structure, which forces Λ to be residually finite.
  Several objects with a Λ-labelled product structure are not effective.
- **The live design.** Cube-type categories whose objects are local states of a Λ-tiling
  (bh-free-36's pointed cube category for cubulated groups is the prototype,
  `cubulated-groups-act-by-bisections-of-a-pointed-cube-category`). Its morphisms are
  rigid extensions of tiles, and Λ acts by bisections.
- **How it links to Strategy 1.** A rigid SFT should give a Li-coded groupoid of
  "extension moves". Proving that correspondence would make G3g a corollary of Li's
  theorem. This is the most promising bridge.

## 4. Strategy 2 (algebraic, characteristic p): algebra BH plus Leavitt transfer

G ↪ F_p[G]^×. If F_p[G] ↪ A, with A a finitely presented simple F_p-algebra such that
L ⊗ A has K₁ = K₂ = 0, then PE_N(L ⊗ A) is a finitely presented simple group
containing G.

**Gates.**
- (A1) algebra BH for group algebras of decidable groups, which is OPEN on main.
  Check the classical literature (Bokut, Belyaev) at source first: a classical algebra
  Higman embedding with simplicity would remove A1.
- (A2) K-theory and stability for L ⊗ A, the same gate as G3r.

**What it supplies.** It avoids dynamics entirely, and the ring-side equivalence
"fp ⇔ quantum rigidity" shows the two strategies meet. The crossed product
LC(X, F₂) ⋊ Λ is one specific A.

## 5. Strategy 3 (structural backup): make BH ⇔ PBH, then close B_A

- **The equivalence.** BH ⇔ PBH is exactly BFFHZ Q3.4 (MIF envelopes), or FFWZ Q5.9
  (kernel removal). The FFWZ non-faithful stabilizer gap flagged by bh-typeA-universal
  needs repair first.
- **Why it's worth closing.** B_A is extraordinarily closed:
  - under products, free products and graph products;
  - under finite-index overgroups;
  - under free, surface and finite-Out hyperbolic kernels;
  - under centralizer amalgams, good coset wreaths, and identity-edge HNN extensions over
    good edges.
- **The only obstruction left.** The one recorded finitely presented simple group not
  known to be in B_A is the Titz Mite–Witzel kernel. Showing it is MIF closes product
  closure and joint embedding for every recorded group.
- **Status.** This strategy does not prove BH. It makes Strategy 1's output maximally
  reusable, and it certifies that no *known* finitely presented simple group separates
  BH from PBH.

## 6. Lane assignment table (proposed; the coordinator decides)

| Gate | Lanes | What each should try |
|---|---|---|
| **G2 rigidity, Z² calibration** | 2 | (a) local-to-global for Labbé: turn the crossing-fault network plus the idempotent ideal into J_D = 0 (`labbe-crossed-product-fp-via-wall-rigidity`); (b) a free minimal *permutive-triangle* SFT (non-sofic rows from bipermutive cellular automata), or a proof that none exists |
| **G2 rigidity, non-amenable** | 2 | (c) a quantum-rigid free minimal SFT over F₂ × F₂ or Λ₀ × F₂, using paradoxical subshifts and compression (which escapes the invariant-measure heuristic); (d) a rigid SFT from building links: Mozes-type SFTs over products of trees or Ã₂ tilings, where the pencil-closure argument gives local-to-global rigidity |
| **G2 obstruction side** | 1 | (e) find an invariant forcing a noncommuting quantum family for *every* free minimal SFT over some Λ (entropy, amenability, periodic quantum tilings). A proof would kill Strategy 1, so it must be tried honestly |
| **G1 existence** | 3 | (f) (M2) an effective minimal free subshift on St₁₀(R_L) (first Kazhdan target) and on general decidable finitely presented groups; (g) (M1) a group simulation theorem over Λ₀ × Z² and Λ₀ × F₂ with *coupled* hierarchy, reading Durand–Romashchenko and Barbieri–Sablik–Salo at source; (h) a *rigid simulation theorem*: does coupling preserve quantum rigidity? |
| **G3g P2′** | 2 | (i) a Stein–Farley / Brown proof of "rigid ⇒ A(G_V × (Λ⋉X)) finitely presented", with Z² Labbé as the test case; (j) the Strategy 1b bridge: rigid SFT ⇒ Li-coded extension category, so Li's theorem gives P2′ |
| **G3r K-theory** | 2 | (k) K₁ = K₂ = 0 for (LC(X,F₂) ⋊ Λ) ⊗ L, reusing the gq stability toolkit; (l) read the Khanh import at source and discharge its conditions |
| **Strategy 2** | 1 | (m) the literature and proof of algebra BH for F_p[G] (Bokut and Belyaev lineage), feeding A2 = G3r |
| **Strategy 3** | 2 | (n) Titz Mite–Witzel kernels are MIF (bh-testcases); (o) the FFWZ gap and kernel removal Q5.9 |
| **Verification** | 2 | adversarial checks of the load-bearing nodes: the necessity theorem, the ring sufficiency theorem, the golden–silver refutation, Labbé wall rigidity, and the Ã₂ link theorem |

That is 17 lanes on the master route. Lanes on isolated test groups (H4, BG, BS(2,3), Out(F_n) stabilizers,
triangle Artin atoms, dendrites) should be retired or re-scoped. Each should ask: "does my group
have a rigid finite-type coding over an fp overgroup?" That question is one instance of G1 plus G2.

## 7. Honest assessment: is BH more likely true or false?

**Leaning true, about 65/35.**

**Reasons for.**
1. **No general obstruction exists.** Every obstruction in the graph is an LRP instance
   aimed at one host family (V-germs, trees, RF, CAT(0), products). None is an invariant
   of finitely presented simple groups in general.
2. **Separators are forced to be exotic.** They must omit nested Kazhdan decidable hosts
   (`bh-separators-must-omit-nested-decidable-hosts`), and they cannot come from any Π₃
   property of presentations (the Σ₃ index-set theorem).
3. **Decidability sits exactly where tilings need it.** Jeandel's duality (strongly
   aperiodic SFT ⇒ decidable) and the fact that the SFT route consumes decidability at
   exactly one gate, G1, are a structural coincidence one expects from a true theorem.
4. **Hard classes keep falling.** Hyperbolic groups, linear groups, all Ã₂ and tree
   lattices, and CT_P(Z) all fell to *rigid codings*, never to ad-hoc tricks.

**Reasons against.**
1. **No rigid example exists yet.** No quantum-rigid free minimal SFT is known over any
   group. For amenable Λ the heuristic points against one: an invariant measure blocks
   compression.
2. **Rigidity may not transfer.** Rigidity may not survive the simulation needed to put
   an arbitrary Λ₀ inside Λ; reading pressure grows exponentially for Λ₀ of exponential
   growth.
3. **BH would force a monster.** BH predicts a single finitely presented simple group that
   is non-exact, not coarsely embeddable, fails BCC, contains an infinite bounded-exponent
   group, and has word problem beyond any recursive bound. None is known.

**What would change the estimate.**
- *Toward true:* one quantum-rigid free minimal SFT over one one-ended non-amenable
  group. That is the single most informative object the swarm could produce.
- *Toward false:* a rigidity obstruction valid for all free minimal SFTs over all
  one-ended groups.

## 8. Sibling synthesis inputs

Reserved for bh-synth-hosts, bh-synth-obstructions and bh-synth-reductions. None had
posted at v1 (10:58 CDT; only a node dump existed in `work/bh-synth-reductions`).
`board/SYNTHESIS.md` carries the live version.
