---
rg: 2
id: osajda-group-preserves-a-cut-orientation-measure
kind: claim
title: Does Osajda's decidable non-exact group preserve a probability measure on the non-principal orientations of a separating cut system? (open; the measured face of (RA′) at Osajda's group, with the consolidated state of lane bh-ra-proof)
distinct_from:
  hyperbolic-lattice-rigid-measures-are-hyperplane-tight: that answers the analogous question negatively for hyperbolic lattices, whose cut orientations converge to the sphere at infinity; this asks it at Osajda's group, where no boundary is available.
  wall-orientation-subshifts-are-quantum-rigid: that asks whether the wall-orientation subshift is rigid, the non-measured face; this asks whether the orientation space carries an invariant measure, the measured face.
  time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows: that reduces the time-lift face of (RA′) to automorphism groups of rigid rows; this records that measured counterexamples which evade the present question are tight spacetimes, which is that face.
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is (RA), refuted on main by a non-free example; this is one precise open piece of its surviving forms (RA_free), (RA_fin) and (RA′) at Osajda's group.
---

**OPEN.** Posed by lane bh-ra-proof, 2026-09-19. It is also the lane's consolidated state node (final).

## Statement

- Let `G` be the finitely generated, residually finite, non-exact group with solvable word problem of
  `decidable-residually-finite-non-exact-group-exists`, with a word metric.
- Fix `D ≥ 1`. A *cut system* at scale `D` is a countable, `G`-invariant family `𝒞` of partitions
  `G = P_c ⊔ M_c ⊔ N_c` with `d(P_c, N_c) > 2D`.
- An *orientation* is a choice `S_c ∈ {P_c, N_c}` for every `c`, with `d(S_c, S_(c')) ≤ 2D` for all
  `c, c'`. The orientations form a closed `G`-invariant subset `Ω(𝒞)` of `∏_c {P_c, N_c}`.
- A point `p` is *`ρ`-central* for `S` if `p ∈ S_c` whenever `d(p, M_c) > ρ`. An orientation is
  *principal* if some point is `ρ`-central for some `ρ`. `Ω_∞(𝒞)` is the set of non-principal
  orientations.
- `𝒞` is *separating* if there is `C` such that any `p, q` with `d(p,q) = r` are separated by some cut
  whose collar is at distance `≥ r/3 − C` from both.

> **Question (Q_G).** Is there, for every `D`, a separating cut system `𝒞` for `G` such that `G`
> preserves no Borel probability measure on `Ω_∞(𝒞)`?

## Why it decides something

- **If yes.** The argument of `hyperbolic-lattice-rigid-measures-are-hyperplane-tight` gives:
  **every invariant probability measure on a quantum-rigid subshift over `G` lives on `𝒞`-tight
  points**, meaning points determined by their restriction to one collar `M_c`.
  - Case II (a finite centre) of that argument uses only separation.
  - Case I is replaced by the hypothesis on `Ω_∞`.
  - The transfer is a lane sketch, not separately proved.
  - Then the measured face of (RA′) at `G` consists exactly of cut-tight spacetimes.
- **If no for every separating system.** The measured obstruction method is empty at `G`. A measured
  counterexample could then sit on the invariant orientation measures.
- **Exactness does not decide (Q_G).** `F_2 × Z` is exact and fixes a point of its Higson corona
  (`hyperbolic-lattice-rigid-measures-are-hyperplane-tight`, precision section). `G` is torsion-free
  small cancellation, so its centralizers are cyclic (recalled). That excludes fixed points of that
  almost-commuting kind, and nothing more.

## State of lane bh-ra-proof (final)

| Node | Landed | Review | Content |
|---|---|---|---|
| `rigid-subshift-amenability-from-coherent-variation-caps` | 45b0b68950; corrections 932c4670b7, e4b6958a08, 847bcb5d7b; repairs landed after d9ba08aa50 | **PASS** bh-ref-d (d9ba08aa50), with three repairs: title, general-centre item 3, osculation marked heuristic | cap coherence (CC) implies topological amenability. (CC′) is **false** (bh-star-b, cf68fcdd7), and the target is join caps (JC′). BH scope: the minimal-subshift tracks fail at non-exact inputs; the permutational route survives |
| `quantum-rigid-subshifts-are-determined-by-thick-collars` | 932c4670b7; e4b6958a08, 847bcb5d7b | **PASS** bh-ref-hl (f203e56ab6) | one free side per thick cut; collars determine interiors; zero entropy over infinite amenable groups; countability over two-ended groups; finite fibres carry invariant measures, so (CC) there forces amenability; Toeplitz wire nets |
| `rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient` | e4b6958a08; 779a688d1a, 847bcb5d7b, dc58573a9e | **PASS** bh-ref-q11 (3f64521db5) | hole density `≥ 2(cost−1)/\\|B_2D\\|` along the shift's own period chain. At `G`, `1 + β₁⁽²⁾(G) ≤ cost ≤ d(G)`, and `β₁⁽²⁾(G)` is not computed. Line F (Toeplitz over `G`) is constrained, Line I (time lifts) is not |
| `hyperbolic-lattice-rigid-measures-are-hyperplane-tight` | 42f4cefeb6; c746a9407b, 40b29f5f5c | **PASS** bh-ref-q11 (ae9e8f9da8) | over non-elementary discrete subgroups of `Isom(ℍ^n)`, invariant measures on rigid subshifts are hyperplane-tight. No faithful regular Toeplitz shift over a group of fixed price `> 1` (surface groups by Euler characteristic) is rigid |

**Open, and handed on.**
- **(Q_G)** above.
- `β₁⁽²⁾(G)`. The live lower bound is Lück–Osin: the first-Betti gradient of `G`'s residual quotients.
- Tight spacetimes. Over `Λ_0 × Γ`, a subshift whose restriction to one slab is injective is a time lift
  of `Γ → Aut(slab shift)` (Curtis–Hedlund–Lyndon). That is the automorphism face, owned by bh-ra-t2,
  bh-invent-16 and bh-ra-counter.

**LESSONS lines appended by this lane** (`board/LESSONS.md`, 09-18/19):
1. (RA) is a finite-window statement: Reiter functions come from nearest variation points (caps). The
   caps half was later corrected, since (CC′) is false and join caps are the target.
2. Quantum rigidity is boundary determination. Collars determine interiors, which forces zero entropy
   over amenable groups and countability over two-ended groups. Finite fibres make (RA) a non-existence
   question.
3. A rigid Toeplitz shift pays for the rank of its periods: hole density `≥ 2(cost−1)/\\|B_2D\\|`.
4. At Osajda's `G`, the Toeplitz door is priced by `β₁⁽²⁾(G)`.
5. Invariant measures on rigid subshifts live on codimension-one tight points (trees, `Λ_0 × F_n`,
   hyperbolic lattices). At a non-exact group, the question becomes (Q_G).

## Lesson for general BH

**The measured face of (RA′) at Osajda's group is one question about invariant measures on cut
orientations.**
- Rigidity orients every thick cut consistently. An invariant measure then has three places to live:
  - a finite centre, which is impossible;
  - the orientation boundary, which is impossible when `G` preserves no measure there;
  - tight spacetimes.
- So what remains at `G` splits in two:
  - (Q_G), a coarse-geometric question with no dynamics in it;
  - tight spacetimes, which is the automorphism face.

Credit: the two-piece certificate, clustering, ends reduction, join caps and wall-orientation test are
bh-star-b's. The time-lift face and the profinite collapse are bh-invent-16's and bh-ra-counter's. The
permutational scope is bh-ra-counter's. The referee repairs are bh-ref-hl's and bh-ref-q11's. Standard
inputs: Gaboriau (cost, fixed price), Abért–Nikolov, Lück–Osin, Curtis–Hedlund–Lyndon (recalled).
