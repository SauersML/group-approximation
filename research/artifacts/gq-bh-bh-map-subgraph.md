# Boone–Higman subgraph on main: status map

Lane `bh-map`, 2026-09-18. Read at origin/main `3903888ab`. No claims of its own.

**Method.**
- Read the root `boone-higman-conjecture` and every node whose id contains
  `boone-higman`, `satisfy-boone-higman`, `bh-`, `pbh` or `shell`: 304 non-proof
  nodes, 191 claims and 113 routes. Also read the 34 routes whose `target:` is the root.
- **Status** is the first status word in each node body (ESTABLISHED, OPEN,
  REFUTED, Proved, known). A `refuted_by:` field counts as refuted.
- **Caveat.** "known" hits were rechecked by hand for every gate in §2; two were in
  fact OPEN. Other "known" labels in §1 come from literature-import nodes.
- **Review column.** "reviewed" means the body records a PASS or a review lane.
  "lane" means the body says not independently reviewed, or shows no review.
  "import" means a literature import.
- **Scope.** The `shell` substring also catches unrelated `shell-pvm` / Hecke nodes
  from other campaigns; those are ignored.
- **Staleness.** The 09-12 artifact `bh-survey-open-cases-status-2026-09-12.md` is
  partly stale, for example on char-0 linear, fp metabelian and spherical Artin.
  Statuses below are at `3903888ab`.

## 1. Status table

### 1a. Classes known to satisfy BH (or permutational BH, "PBH") on main

| Class | Node | Status | Review |
|---|---|---|---|
| Hyperbolic groups | `hyperbolic-groups-satisfy-boone-higman` | ESTABLISHED | import (BBMZ) |
| Aut(F_n), hence braid groups, punctured/bounded MCGs, Artin A_n, B_n, D_n, I_2(m), Ã_n | `aut-free-groups-satisfy-permutational-boone-higman`, `punctured-surface-mcgs-satisfy-permutational-boone-higman` | ESTABLISHED | import (BFFHZ) |
| All BS(m,n), free-by-cyclic, virtually free-by-cyclic | `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`, `virtually-free-by-cyclic-groups-satisfy-boone-higman` | ESTABLISHED | import (Bux–Llosa Isenrich–Wu) |
| f.g. subgroups of GL_n(Q) | `rational-linear-groups-satisfy-boone-higman` | ESTABLISHED | import (Zaremsky 2405.09722) |
| f.g. linear over number fields | `algebraic-linear-groups-satisfy-boone-higman` | ESTABLISHED | lane |
| f.g. linear, any field of char 0 | `char-zero-linear-groups-satisfy-boone-higman` (via `polynomial-linear-groups-satisfy-boone-higman`) | ESTABLISHED 09-12 | reviewed (`bh-poly-linear-review`) |
| f.g. linear, positive char / char 2 | `positive-char-linear-groups-satisfy-boone-higman`, `char-two-linear-groups-satisfy-boone-higman` | ESTABLISHED 09-12 | lane (partly conditional on imports) |
| PBH for char-0, char-p and quasi-linear groups | `char-zero-linear-…-permutational-…`, `char-p-linear-…-permutational-…`, `quasi-linear-groups-satisfy-permutational-boone-higman` | ESTABLISHED 09-13 | quasi-linear reviewed; others lane |
| f.p. metabelian (BBMZ 5.3(7)) | `fp-metabelian-groups-satisfy-boone-higman` | ESTABLISHED 09-13 | reviewed (PASS lines) |
| Baumslag's char-0 metabelian group | `baumslag-char-zero-metabelian-group-satisfies-boone-higman` | ESTABLISHED 09-12 | lane |
| Soluble groups linear over global-field products | `global-field-soluble-linear-products-satisfy-boone-higman` | ESTABLISHED | reviewed |
| Free soluble groups; product-variety free groups | `free-solvable-groups-satisfy-permutational-boone-higman`, `product-variety-free-groups-…` | ESTABLISHED | lane |
| Spherical Artin (incl. E_6–E_8) | `spherical-artin-groups-satisfy-boone-higman`, `e-type-artin-groups-satisfy-permutational-boone-higman` | ESTABLISHED | E-type reviewed; spherical lane |
| Euclidean Artin B̃_n, C̃_n; even FC Artin | `b-tilde-…`, `c-tilde-…`, `even-fc-artin-groups-satisfy-permutational-boone-higman` | ESTABLISHED / Proved | C̃ reviewed; B̃, even-FC lane |
| Druţu–Sapir group | `drutu-sapir-group-satisfies-boone-higman` | ESTABLISHED 09-13 | reviewed |
| Virtually fibered 3-manifold groups (PBH) | `virtually-fibered-3-manifold-groups-satisfy-pbh` | ESTABLISHED 09-13 | lane |
| Cocompact lattices in a product of two trees (PBH) | `product-of-two-trees-lattices-satisfy-permutational-boone-higman` | ESTABLISHED | lane |
| Product-of-trees lattices with a faithful factor (PBH) | `product-of-trees-lattices-with-faithful-factor-satisfy-pbh` | ESTABLISHED | lane |
| Leavitt units / F_p (and squares), Kac–Moody, Lodha S, Stein F_{2,3}, F_τ (PBH) | `leavitt-unit-groups-mod-scalars-satisfy-pbh`, `fp-simple-kac-moody-lattices-satisfy-pbh`, `lodha-circle-group-satisfies-pbh`, `stein-and-irrational-slope-f-groups-satisfy-pbh` | ESTABLISHED | mostly lane |
| Subgroups of f.p. self-similar groups (PBH) | `fp-self-similar-subgroups-satisfy-permutational-boone-higman` | ESTABLISHED | lane |
| Power-map mapping tori; MIF-free-product HNNs; outer extensions of MIF groups (PBH) | `power-map-free-mapping-tori-…`, `mif-free-product-automorphism-ascending-hnn-is-pbh`, `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh` | ESTABLISHED | lane |

### 1b. OPEN class nodes

| Class (named item) | Node |
|---|---|
| MCGs of closed surfaces, genus ≥ 3 (BBMZ 5.3(2)) | `closed-surface-mapping-class-groups-satisfy-boone-higman` |
| Out(F_n), n ≥ 3 (5.3(3)); gate `out-free-groups-virtually-embed-in-aut-free-groups` | `out-free-groups-satisfy-boone-higman` |
| GL_n(Q) itself (5.3(5), p. 7) | `gl-n-q-embeds-in-fp-simple-group` (gq swarm) |
| Free Burnside B(m,n) with solvable WP (5.3(6)) | **no BH node** |
| Torsion-free one-relator (5.3(9)); Baumslag–Gersten | `one-relator-groups-satisfy-boone-higman`, `baumslag-gersten-group-satisfies-boone-higman` |
| CAT(0) (5.3(10)); exotic Ã_2, Titz–Witzel, vertex-free rotating Ã_2 | `cat0-groups-satisfy-boone-higman`, `exotic-a2-lattices-…`, `titz-witzel-lattices-…`, `vertex-free-type-rotating-a2-groups-…` |
| Automatic (5.3(11)) | `automatic-groups-satisfy-boone-higman` |
| f.p. residually finite (5.3(12)); its A_p²A case | `fp-residually-finite-boone-higman`, `fp-rf-apapa-groups-satisfy-boone-higman` |
| Artin groups with solvable WP (5.3(13)); admissibly oriented | `artin-groups-satisfy-boone-higman`, `admissibly-oriented-artin-groups-satisfy-boone-higman` |
| Compact 3-manifold groups; non-fibered graph manifolds (PBH) | `compact-3-manifold-groups-satisfy-pbh`, `nonfibered-closed-graph-manifold-groups-satisfy-pbh` |
| Higman's group; Deligne's lattice | `higman-group-satisfies-boone-higman`, `deligne-lattice-satisfies-boone-higman` |
| Products of trees in general; free centre-by-metabelian; V_τ, V_{2,3} subgroups; F_p Leavitt units (PBH) | `product-of-trees-lattices-satisfy-permutational-boone-higman`, `free-centre-by-metabelian-groups-satisfy-boone-higman`, `irrational-slope-v-tau-subgroups-satisfy-pbh`, `stein-group-v23-subgroups-satisfy-pbh`, `prime-field-leavitt-unit-groups-satisfy-pbh` |
| Closure of BH under finite direct products (6 attempts) | `boone-higman-closed-under-finite-direct-products` |
| Rings: char-0 ring BH, algebra BH | `char-zero-ring-boone-higman`, `algebra-boone-higman-conjecture` |

### 1c. Equivalences and reductions of BH (all ESTABLISHED unless marked)

- **Simple inputs.** BH ⟺ BH for infinite f.g. computably presented simple groups
  (`boone-higman-iff-infinite-simple-inputs`, 08-30).
- **Simple Kazhdan inputs.** BH ⟺ BH for infinite f.g. simple groups with property (T)
  and solvable WP (`boone-higman-iff-simple-kazhdan-decidable-inputs`).
- **Just-infinite hosts.** BH ⟺ every decidable f.g. group embeds in an f.p.
  just-infinite group (`boone-higman-iff-fp-just-infinite-hosts`).
- **Local BH.** BH ⟺ every finite system of equations and inequations, even a single
  inequation, solvable over an f.p. decidable group is solvable in an f.p. simple group
  (`local-boone-higman-iff-boone-higman`).
- **Isolated hosts.** BH ⟺ Cornulier–Guyot–Pitsch Question 4 (every decidable group
  embeds in an isolated group) plus Local BH
  (`boone-higman-iff-isolated-hosts-and-local-boone-higman`).
- **Simple FA inputs.** Every decidable group embeds in a decidable simple FA group
  (`decidable-groups-embed-in-decidable-simple-fa-groups`, ESTABLISHED). So BH ⟸
  `simple-fa-input-boone-higman` (OPEN).
- **Countable inputs.** Countable decidable ⇒ f.g. via HNN (route
  `countable-decidable-bh-from-boone-higman`; BBMZ Cor. 3.5).
- **Permutational BH.**
  - PBH = every decidable group embeds in an f.p. group with a type (A) action
    (`permutational-boone-higman-conjecture`, OPEN).
  - PBH ⟺ finitary-alternating f.p. permutation hosts
    (`permutational-boone-higman-iff-finitary-alternating-hosts`).
  - PBH for a group ⟺ it embeds in an f.p. simple highly transitive / MIF group
    (`fp-simple-highly-transitive-groups-satisfy-pbh`, import).
  - BH ⇒ PBH iff every f.p. simple group embeds in an f.p. simple highly transitive
    group (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`).
- **Kazhdan BH.** `kazhdan-boone-higman-conjecture` (OPEN) ⇒ BH. The CK finite
  bi-index hole ⇒ Kazhdan BH, with equivalence when the core is free
  (`ck-finite-bi-index-hole-is-kazhdan-boone-higman`).
- **Towers and HNNs.** Edge membership must be decidable for HNNs over f.g. edges
  (`bh-embeddability-forces-decidable-edge-membership`). The decidable-edge tower
  premise ⟺ BH (`decidable-edge-tower-premise-is-equivalent-to-boone-higman`, OPEN
  as stated). Magnus-HNN permanence ⇒ one-relator BH
  (`magnus-hnn-permanence-forces-one-relator-boone-higman`, conditional theorem).
- **Separators (limits on disproof).**
  - Hereditary approximation properties forcing soficity or MF cannot disprove BH
    (`hereditary-approximation-disproofs-of-boone-higman`).
  - Exactness disproves BH iff every f.p. simple group is exact
    (`exactness-separates-boone-higman-iff-fp-simple-groups-exact`, unreviewed).
  - Følner-growth and random-walk separators fail
    (`folner-separators-of-boone-higman`, `random-walk-separators-of-boone-higman`).
- **PBH closure.** Graph products, common-retract amalgams, relative holomorphs,
  wreath products with finite stabilizers, finite extensions and products. Permutational
  wreaths with infinite stabilizers are OPEN.
- **Finite-state limit.** Some decidable f.p. RF groups embed in no rational group
  (`decidable-fp-groups-need-not-embed-in-rational-group`, cited in the root).

## 2. Routes to the root and their open gates

**Dead, because a requirement is refuted:**
- `via-complexity-graded-universal-inputs`;
- `via-rover-nekrashevych-hosts`;
- `via-universal-fp-self-similar-host` (`every-decidable-group-embeds-in-fp-self-similar-group` refuted);
- `via-shift-higman-compiler` (as written);
- `via-bffhz-action-image`;
- `via-ck-quotient-cosets`;
- `via-ck-maximal-kernel`;
- `via-finitely-presented-simple-ring-quotient`;
- `via-v-times-aperiodic-sft-full-groups` (`v-times-minimal-free-sft-alternating-full-groups-are-fp` has refuted_by).

**Live. Each gate is one precise question:**
1. **Perfect shell** (`via-perfect-shell-envelopes`). For every infinite perfect f.p.
   decidable P, is there an enumeration ν with the shell envelope E_ν f.p.?
   (`perfect-decidable-inputs-have-fp-shell-envelopes`.) E_ν is already simple.
2. **Shell, general** (`via-fp-shell-envelopes`, `via-shell-germ-stabilizers`,
   `via-enlarged-shell-stabilizers`, `via-shell-stabilizer-overgroups`). Can ν be chosen
   so that one of these holds?
   - the one-singularity stabilizer is f.p. (`decidable-inputs-have-fp-shell-stabilizers`);
   - the envelope is f.p. (`decidable-inputs-have-fp-shell-envelopes`);
   - the perfect shell action has an f.p. permutation extension
     (`perfect-shell-actions-have-fp-permutation-extensions`);
   - a finite-bi-index f.p. host exists (`perfect-shell-pairs-have-finite-biindex-fp-hosts`).
   The germ-group gate `shell-germ-fp-is-an-ascending-hnn-gate` sharpens the first, and
   `free-shift-shell-envelopes-are-not-finitely-presented` kills the generic ν.
3. **PBH** (`via-permutational-boone-higman`). Does every decidable group embed in an
   f.p. type-(A) actor?
4. **Kazhdan BH** (`via-kazhdan-boone-higman`). Is there an f.p. simple (T) host?
   Also `via-finite-bi-index-envelope`: does the CK envelope's simple core have finite
   bi-index (`ck-envelope-simple-core-has-finite-bi-index`)?
5. **Simple inputs.** Do infinite computably presented simple groups (or simple FA
   ones) embed in f.p. simple groups? (`infinite-simple-input-boone-higman`,
   `simple-fa-input-boone-higman`.)
6. **Local / isolated** (`via-local-boone-higman`,
   `via-isolated-overgroup-and-local-boone-higman`). Is every single-inequation system
   solvable over an f.p. decidable group solvable in an f.p. simple group? Does every
   decidable group embed in an isolated group (CGP Q4)?
7. **Towers.** Does every decidable group embed in a decidable-edge tower, and do HNNs
   over decidable f.g. edges preserve f.p.-simple embeddability?
   (`decidable-groups-embed-in-decidable-edge-towers`, `bh-embeddability-survives-decidable-edge-hnn`.)
8. **Lattice hosts** (`via-bader-shalom-lattice-hosts`). Do decidable simple groups
   embed in Bader–Shalom product lattices? Does simplicity there force compact
   presentation?
9. **Ring and Leavitt hosts.** Do decidable group algebras have f.p. central-simple
   hosts (`decidable-group-algebras-have-fp-central-simple-hosts`)? Do decidable groups
   lie in f.p. free minimal crossed products, or in Cantor-crossed Leavitt tensor unit
   groups (`decidable-groups-lie-in-fp-free-minimal-crossed-products`,
   `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`,
   `free-action-leavitt-tensor-hosts-have-trivial-k1-k2`)? Does the decidable group
   ring have an f.p. projective simple host (`decidable-group-ring-has-fp-projective-simple-host`)?
10. **Fiber product** (`via-fiber-product-criterion`). Does every decidable f.g. G lie
    in an f.p. T with f.g. normal N ⊴ T, T/N of type F_3, C_T(N) = 1 and finitely many
    T-classes in N? (`universal-fiber-product-data-for-word-problem-groups`, an OPEN
    construction problem. Clauses 5–6 pull against clause 3; see
    `some-fp-group-has-centralizer-free-class-finite-normal-subgroup`, OPEN.)
11. **Infinite shift compiler** (`via-infinite-shift-compiler`). For every infinite
    f.p. decidable P, is there ν: P → N with the Mallery–Zaremsky group E_ν(P) f.p.?
    (`infinite-shift-higman-compiler`, OPEN. Every other clause is free by Zaremsky
    2405.18354 Prop. 5.3.)
    *Correction during drafting:* a first status parse read these two gates as "known",
    because of that word in their bodies. Both are OPEN. No route to the root has all
    requirements established.

## 3. Named problems and their status on main

BBMZ, *Progress around the Boone–Higman conjecture*, arXiv:2306.16356. Problem 5.3
(p. 17) and neighbors, with verbatim wording in `bh-survey-open-cases-status-2026-09-12.md` §1:

| Item | Status at `3903888ab` |
|---|---|
| 5.3(1) braid groups | settled (BFFHZ) |
| 5.3(2) MCGs | settled with a puncture or boundary and for closed genus ≤ 2; **open for closed genus ≥ 3** |
| 5.3(3) Aut(F_n), Out(F_n) | Aut settled; **Out(F_n), n ≥ 3, open** |
| 5.3(4) BS(m,n) | settled (BLIW) |
| 5.3(5) GL_n(Q) | f.g. subgroups settled (Zaremsky); **GL_n(Q) itself open** (gq swarm). The explicit f.p. overgroup of Problem 2.7 / Kourovka 14.10(c) is ESTABLISHED on main (`gl-n-q-explicit-natural-fp-overgroup`) |
| 5.3(6) free Burnside groups with solvable WP | **open; no BH node on main** |
| 5.3(7) f.p. metabelian | **ESTABLISHED on main** (`fp-metabelian-groups-satisfy-boone-higman`, reviewed; external priority not checked by this lane) |
| 5.3(8) free-by-cyclic | settled (BLIW) |
| 5.3(9) torsion-free one-relator | **open**; reduces to Magnus-HNN permanence |
| 5.3(10) CAT(0) | **open**; two-tree lattices done (lane) |
| 5.3(11) automatic | **open** |
| 5.3(12) f.p. residually finite | **open** |
| 5.3(13) Artin with solvable WP | spherical (all), B̃_n, C̃_n, Ã_n, triangle and even-FC done on main (partly lane); **D̃_n, Ẽ_6–Ẽ_8, F̃_4 and general types open** |
| Remark 5.5 (PIP homeomorphisms) | open (closed-MCG attempts) |
| Question 5.6 (every f.p. group ⊂ type F∞?) | open; only `cardinality-does-not-obstruct-type-f-infinity-embedding` bears on it |
| Question 4.7 (one-ended hyperbolic groups in V) | open; no node |

Other named questions on main:
- **Cornulier–Guyot–Pitsch Question 4 (isolated groups).** OPEN
  (`every-decidable-group-embeds-in-an-isolated-group`); a conjunct of BH.
- **BFFHZ Question 3.4.** Answered conditionally, through PBH
  (`fp-simple-mif-embedding-via-permutational-boone-higman`).
- **Zaremsky Problem 2.14.** Answered by BH plus Kuznetsov
  (`zaremsky-2-14-by-boone-higman`).

## 4. Ten sharpest open questions

Ranked by (chance a lane decides it) × (impact on BH), highest first.

1. **Free Burnside B(m,n), BBMZ 5.3(6).** No node exists. Deciding which B(m,n) with
   solvable WP embed (odd n ≥ 665, via hyperbolic approximation and Olshanskii–Ivanov
   theory) is a clean named item with nothing on main. High chance of at least a
   reduction.
2. **Infinite shift compiler, route 11.** Choose ν so the Mallery–Zaremsky E_ν(P) is
   f.p. It is the same "one explicit family" shape as the perfect shell route. It
   shares that route's germ and near-relation tools
   (`infinite-order-inputs-admit-mixed-near-relations`), and sits one clause from BH.
3. **One-relator, 5.3(9).** `bh-embeddability-survives-magnus-subgroup-hnn` suffices
   (conditional theorem ESTABLISHED). One permanence theorem for Magnus-subgroup HNNs
   of f.p.-simple-embeddable groups would settle a survey item.
4. **Out(F_n), 5.3(3).** `out-free-groups-virtually-embed-in-aut-free-groups` would
   finish it via BFFHZ. This is a concrete geometric-group-theory question.
5. **BH for finite direct products** (`boone-higman-closed-under-finite-direct-products`,
   6 attempts). This basic closure property is open, and PBH is closed under products,
   so the gap is BH-without-(A).
6. **Closed MCGs, genus ≥ 3, 5.3(2).** Open after five attempts. Remark 5.5 (PIP
   groups) and Out(F_n)-style embeddings are the known levers.
7. **Perfect shell envelopes** (route 1). The most general live constructive route;
   E_ν is simple for every ν. The whole conjecture sits in finite presentation of one
   explicit group family. The St_N(R_L) instance (gq) is the test case.
8. **D̃_n, Ẽ-type and F̃_4 Euclidean Artin groups (5.3(13) remainder).** Fibration or
   folding tricks settled B̃ and C̃; the known blockers are listed in the survey
   artifact §4.
9. **Automatic groups (5.3(11)) or CAT(0) groups (5.3(10)).** Both contain closed
   MCGs or E-type Artin groups. A special subclass, such as cocompactly cubulated
   (virtually special, hence linear, hence ESTABLISHED via char-0 linear), should be
   recorded explicitly, and the genuine gap isolated (non-special CAT(0), non-linear
   automatic).
10. **f.p. residually finite groups (5.3(12)).** Any positive construction must beat
    the KMS hardness limits (`decidable-fp-groups-need-not-embed-in-rational-group`).
    Lower chance but high impact, and it shares machinery with the gq Z_(l) bottleneck.
