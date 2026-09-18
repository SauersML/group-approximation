# Boone–Higman test cases: the simplest explicit inputs where BH is not known

Lane `bh-testcases`, 2026-09-18. Read from origin/main node bodies (status lines as
printed). No claims of my own except the two new OPEN nodes below. Facts marked
"textbook" are recalled, not pinned at source.

## Ranking criterion

A test case ranks high if (a) it is one explicit group, ideally finitely presented
with a short presentation, (b) many host families are already provably dead for it,
so any success needs a genuinely new host, and (c) it is a named problem or sits on
a BH equivalence. Rank = how much a solution for it would teach about BH itself.

## Ranked list

| # | Test case | Explicit form | Named? | Node | Dead hosts (node) | Still open |
|---|---|---|---|---|---|---|
| 1 | Higman group `H4` | 4 gens, 4 relators; poly-time WP | no | `higman-group-satisfies-boone-higman` | RF/linear/self-similar (no finite quotients); all almost-automorphism `A_(d,r)` (`higman-group-embeds-in-no-almost-automorphism-group`); piecewise-analytic circle groups incl. `T`, Lodha `S`; `nV` reduced to four zero-entropy BS(1,2) witnesses | twisted BT over an f.p. type (A) actor ⊇ `H4`; groupoid full groups with non-equicontinuous generators |
| 2 | Baumslag–Gersten `BG` | 2 gens, 1 relator; non-RF | 5.3(9) (one-relator) | `baumslag-gersten-group-satisfies-boone-higman` | tree hosts (base elliptic); linear/self-similar; odometer/affine models; Röver–Nekrashevych, `V`, `T`, `F` (`baumslag-gersten-embeds-in-no-rover-nekrashevych-group`); graph path-space hosts; piecewise-analytic circle | a host where `a` is non-equicontinuous; `BG/<<t^4>> ≅ H4 ⋊ C4` (`baumslag-gersten-group-maps-onto-higman-groups`, bh-free-35), so a type (A) actor containing `H_n ⋊ C_n` settles `H_n`; `BG` is highly transitive and MIF (`baumslag-gersten-group-is-highly-transitive-and-mif`); one-relator permanence (`magnus-hnn-permanence-forces-one-relator-boone-higman`) |
| 3 | Free Burnside `B(2,665)` | 2 gens, infinite exponent law; solvable WP | **5.3(6)** | **new:** `free-burnside-groups-satisfy-boone-higman` | linear (Burnside–Schur); RF/self-similar (Zelmanov); hyperbolic (finite torsion subgroups); cubulated (Sageev–Wise) | any host realizing infinite bounded-exponent periodicity without a rooted tree; uniform host for the hyperbolic tower |
| 4 | Deligne lattice `Γ~` over `Sp_4(Z)` | f.p., (T), infinite center, non-RF | no | `deligne-lattice-satisfies-boone-higman` | RF/linear/self-similar; Röver–Nekrashevych (`deligne-lattice-embeds-in-no-rover-nekrashevych-group`); amenable-orbit full groups (Kazhdan subgroups RF); `Γ~` as its own type (A) actor (`type-a-actors-have-no-infinite-virtually-central-subgroup`) | shell premise for full Cantor hosts with non-amenable orbits |
| 4a | Torelli quotient `Q_(g,2)`, `g ≥ 3` | f.g., (T), not linear, not RF, solvable WP (bh-free-38) | no (Nowak 2026) | `torelli-lower-central-quotients-satisfy-boone-higman` | all RF hosts; Röver–Nekrashevych; every host whose Kazhdan subgroups are RF or finite; contains a Deligne-type lattice mod a finite centre (`torelli-lower-central-quotients-are-not-residually-finite`) | same as Deligne; no tree action, so the tree methods below cannot reach it |
| 5 | Osajda decidable non-exact `G` | f.g., RF, decidable, non-exact | on the exactness separator | **new:** `osajda-decidable-nonexact-group-satisfies-boone-higman` | linear, hyperbolic, cubulated, amenable-action hosts (all exact) | any host is an f.p. simple non-exact group, itself open (`fp-simple-nonexact-group`) |
| 6 | `Out(F_3)` | f.p., non-linear for n ≥ 4 (n = 3 open) | **5.3(3)** | `out-free-groups-satisfy-boone-higman` | none decisive; `Aut(F_n)` done (BFFHZ) | `out-free-groups-virtually-embed-in-aut-free-groups` would finish it |
| 7 | `Mod(Σ_3)` closed | f.p., linearity open | **5.3(2)**; also 5.3(11), since MCGs are automatic (Mosher, textbook) | `closed-surface-mapping-class-groups-satisfy-boone-higman` | punctured case done (literature import); closed open after five attempts | PIP homeomorphisms of the Thurston sphere (survey Rem. 5.5) |
| 8 | Exotic Ã₂ lattices / CMSZ groups | f.p., (T), only finite linear images | 5.3(10) subcase | `exotic-a2-lattices-satisfy-boone-higman`, `vertex-free-type-rotating-a2-groups-satisfy-boone-higman` | linear (BCL), tree (T ⇒ FA), hyperbolic, self-similar | Robertson–Steger 2-graph full groups (reduction on main, one OPEN input) |
| 9 | `GL_2(Q)` / `SL_2(Q)` | countable, not f.g. | **5.3(5)** | `gl2-q-embeds-in-fp-simple-group`, `sl2-q-embeds-in-fp-simple-group` | RF hosts (divisible Q); V, VA; torus/Borel amalgams (gq swarm) | St_N(R_L) shell envelope (gates on main) |
| 10 | Free centre-by-metabelian `C_2` | solvable, derived length 3 | first uncovered solvable case | `free-centre-by-metabelian-groups-satisfy-boone-higman` | see node | see node |
| 11 | Ẽ-type, F̃_4, D̃_n Artin groups | f.p., solvable WP (Euclidean types) | **5.3(13)** remainder | `artin-groups-satisfy-boone-higman` | see node | fibration/folding tricks that settled B̃, C̃ |
| 12 | f.p. RF groups with hard WP (KMS groups) | f.p., RF | **5.3(12)** | `fp-residually-finite-boone-higman` | rational (finite-state) homeomorphism hosts (`decidable-fp-groups-need-not-embed-in-rational-group`) | non-finite-state Cantor hosts |
| — | Amir–Lazarovich `Λ'` (and its simple `Λ`) | f.p., virtually simple, not RF, torsion; uniform lattice in `Aut(T_c) × Aut(X_(O_d))` | Kourovka 21.46 context (cd 3) | **decided 09-18:** `tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh` | — | **in `B_A`**: just-infinite ⇒ faithful on `T_c` ⇒ BLIW tree criterion; so `Λ'`, `Λ^k`, `Λ' × (B_A)` embed in f.p. simple groups |

## Reading

- **The two non-RF one-relator-sized groups (`H4`, `BG`) are the sharpest single
  tests.** Every host family with an equicontinuity or rooted-tree mechanism is
  dead for them, and both force `BS(1,2)` with a non-equicontinuous generator. A
  host for either must be a new kind of Cantor dynamics. The 2V_τ host
  (`odometer-2v-is-fp-simple-and-contains-bs12`) contains `BS(1,2)` but its
  odometer generator `τ×id` is equicontinuous, so it is not yet a candidate.
- **`B(2,665)` is the cleanest named item with no prior node.** It is the only
  test here that kills every host through torsion plus the failure of residual
  finiteness at once, while torsion alone is known not to be an obstruction
  (Röver's group contains Grigorchuk's group).
- **`Γ~` and the Ã₂ lattices test rigidity.** (T) kills tree and amenable-orbit
  hosts, and the infinite center of `Γ~` kills it as its own type (A) actor.
- **The Osajda group tests analytic properties.** It is residually finite, so none
  of the combinatorial kills apply, but every known f.p. simple group has unknown
  exactness. Settling exactness of `V` or `nV` either way would move this row.
- **Named items 5.3(2), (3), (5), (6), (9), (10), (11), (12), (13)** all appear
  above through a representative. Items (1), (4), (7), (8) are settled on main
  (braid via BFFHZ, BS and free-by-cyclic via BLIW, f.p. metabelian via
  `fp-metabelian-groups-satisfy-boone-higman`).

## Candidates considered and not listed

- Burger–Mozes and product-of-two-trees lattices: covered by
  `product-of-two-trees-lattices-satisfy-permutational-boone-higman`, and many are
  f.p. simple themselves.
- Kac–Moody lattices over finite fields: f.p. simple (Caprace–Rémy), trivially BH.
- Titz Mite–Witzel lattices: node exists (`titz-witzel-lattices-satisfy-permutational-boone-higman`, OPEN).
- Tarski monsters and Nekrashevych's simple groups of intermediate growth: not
  listed, because I could not confirm solvable word problem for a specific
  construction at source. They sit in the BH-equivalent class of infinite simple
  inputs (`boone-higman-iff-infinite-simple-inputs`).

## Update 2026-09-18 (free mode)

**New rows.** `Q_(g,2)` (4a, bh-free-38), the `BG ↠ H4 ⋊ C4` link (row 2, bh-free-35), and the
Amir–Lazarovich lattices. The Amir–Lazarovich row is decided: `Λ'` acts faithfully on its tree
factor because it is just-infinite, and a cocompact lattice on `T × Y` with a faithful tree factor
is in `B_A` (`tree-by-complex-lattices-with-faithful-tree-factor-satisfy-pbh`).

**New constraints on row 1 (`H4`), all lane proofs.**
- `equicontinuous-bs-bases-force-conjugator-entropy`: in finite-entropy hosts, no generator is an
  odometer-type equicontinuous map.
- `twisted-brin-thompson-labels-are-rigid`: in `SV_G` with `G ∩ FSym(S) = 1`, a pure-label generator
  must already be conjugate to its square in `G`.
- `odometer-2v-orbit-action-is-type-a`: `SV` over `2V_tau` is an f.p. simple host with an
  infinite-entropy `BS(1,2)` base.
- `higman-images-in-brick-hosts-have-iterated-log-growth` and
  `brin-thompson-aperiodic-elements-have-logarithmic-movement`: in `nV`, the generators move
  `≥ log N/(2n)` infinitely often, but `O((log m)^2)` at the times `2^m`.

**Most within reach next** (bh-testcases' judgement).
- Lattices on `T × Y` whose tree factor is not faithful and not just-infinite. The kernel is the
  only gap.
- Titz Mite–Witzel lattices, if any of them have a tree factor. Not checked.
