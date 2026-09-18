# bh-g1-simulation: gate G1(g), coupled simulation (2026-09-18)

Lane `bh-g1-simulation` of the master route (`research/artifacts/gq-bh-synthesis-master-route.md`,
gate G1(g)): a group simulation theorem over `Λ_0 x Z^2` and `Λ_0 x F_2` with a coupled
hierarchy. Everything below is a lane analysis and is unreviewed.

## 1. Sources read (TeX, via the msi wrapper)

Stored on MSI in `gqsrc/bh-g1-simulation/`, with local copies in `$GQ/src/bh-g1-simulation/`.

| Source | File | md5 |
|---|---|---|
| Jeandel, arXiv:1501.06831 | `groups.tex` | 7ddfd362… |
| Durand–Romashchenko, arXiv:1802.01461 | `arxiv-4.tex` | 8e17f728… |
| Barbieri–Sablik–Salo, arXiv:2104.05141 | `self_simulation_main.tex` | c38dd87a… |

**What each gives.**
- **Jeandel.** Theorem `cor:final` and its corollary: a recursively presented group with
  a normally aperiodic effectively closed subshift, in particular one with a strongly
  aperiodic SFT, has decidable word problem. This confirms the "decidability is consumed
  at G1" point of the synthesis.
- **Durand–Romashchenko.**
  - Theorem `thm-main-min`: every effective minimal `Z^d`-shift is simulated by a
    minimal SFT in `Z^(d+1)`.
  - Minimality is enforced in §`ss-3-2`, by case analysis on `2x2` blocks of macro-tiles:
    skeleton, communication wires, computation zone. The computation-zone case uses
    *diversification slots*, isolated `2x2` copies of every legal computation-zone
    window placed in the free zone of each macro-tile.
  - Letter delegation for codimension-1 subdynamics is in §`subsection:delegation`.
- **Barbieri–Sablik–Salo.**
  - Theorem `thm:selfsimulation`: every product of two finitely generated non-amenable
    groups is self-simulable, i.e. every effectively closed action is a factor of an SFT.
  - Proof ingredients:
    - the paradoxical subshift, which encodes bounded 2-to-1 maps and so gives disjoint
      one-sided paths (Proposition `prop_ceccSilb`, Lemma `lem:injectivepaths`);
    - `N^2`-grids from products of paths;
    - seeded Wang computations with a synchronization layer (constant antidiagonals);
    - coherence rules between the grids of `g` and `gs^-1`, for each generator `s`.
  - There is **no hierarchy**.
  - Corollary `cor:stronglyaperiodic`: a self-simulable group with decidable word
    problem carries a strongly aperiodic SFT.
  - Proposition `prop:villexample`: `F_k x Z` is **not** self-simulable.
  - Question `Q:minimal` asks for minimal (respectively transitive) SFT extensions. BSS
    name two obstacles:
    - **(a)** bi-infinite paths are unavoidable, and their computation contents are
      unrestricted;
    - **(b)** return times of the input and of the geometry can synchronize.
  - They state, without proof, a minimal paradoxical SFT `M` on `F_2`.

**Correction.** Attempt 1 of `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`
cited BSS for strongly aperiodic SFTs on `Λ_0 x Z`. BSS do not give that. They give it
when both factors are non-amenable, and they prove `F_k x Z` is not self-simulable. The
conclusion of Attempt 1 is unaffected.

## 2. New nodes

- **`simple-subgroups-act-trivially-on-equicontinuous-factors`** (ESTABLISHED, lane
  proof).
  - A minimally almost periodic subgroup acts trivially on the maximal equicontinuous
    factor of every minimal action.
  - Every infinite f.g. simple group is minimally almost periodic (Peter–Weyl plus
    Malcev).
  - Consequences:
    - free minimal actions of groups containing such a subgroup are never almost
      automorphic;
    - functional plane couplings over almost-automorphic transverse layers (e.g.
      Labbé's shift) kill the input.
- **`nonamenable-products-have-minimal-sft-extensions-of-free-inputs`** (OPEN). BSS's
  printed `Q:minimal`, restricted to products of two non-amenable groups and to free
  expansive inputs, with the design constraints below.
- **`minimal-free-sft-via-minimal-self-simulation-of-squares`** (route to
  P1). Existence reduces to (M2) for the Clapham envelope `Λ_1` of `K x F_2`, plus the
  premise above for `Λ_1 x Λ_1`.

## 3. Design analysis: one crux in three settings

**(A) Plane-constant DR over `Λ_0 x Z^2`** (the existing M1 route).
- The floating locus is the `Y`-data on infinite active father-chains, indexed by planes.
- Deterministic completion is killed by `injective-plane-lift-codings-force-finite-type`.
- Plane-independent diversification slots give only constant tuples (crux node).
- Functional coupling of planes by an almost-automorphic `Z^2`-layer is killed by the
  new lemma, part 3.

**(B) BSS grids with geometry constant along the input factor** (paths only in a
transverse `H`, e.g. `Λ_1 x F_2 x F_2` with `BSS-M x BSS-M` as geometry).
- The geometry is minimal: a product of minimal systems for the product group.
- Suppose every cell is reached at finite depth. Then the point is determined by the
  `Y_1`-coordinate and the transverse data. This is setting (A) with `H` in place of
  `Z^2`, and the injective-plane-lift argument then forces `Y_1` to be of finite type.
  - Not re-proved for general `H`; the proof reads as using only countability of `H`.
- So removing the floating locus makes things worse. Floating is necessary, and its
  diversification is the crux again.

**(C) BSS grids with paths in both factors** (`Λ_1 x Λ_1`).
- No plane structure, so (A)'s kill does not apply. The needs are:
  1. **A minimal paradoxical SFT on each factor.** Proved here: paradoxical subshifts
     have no finite orbits, because a finite-index-invariant bounded 2-to-1 map descends
     to a 2-to-1 self-map of a finite set. So the geometry is an infinite minimal SFT
     without invariant measure. For Kazhdan simple envelopes none is known.
  2. **Fixed-point tilings in place of seeds (proposal).** A DR fixed-point tiling inside
     each grid, with letters constant along one grid direction, is valid on `N^2`,
     `Z x N` and `Z^2`. This removes obstacle (a)'s junk.
  3. **Obstacle (b), as a phase field.**
     - Anchored grids can align their hierarchy with the corner, so their phase is
       determined. Unanchored grids carry free phases.
     - Local rules relate neighbouring phases by closed relations `R_s`. Heuristic
       trichotomy:
       - no relation: synchronized configurations break minimality;
       - equality: an invariant phase function breaks minimality;
       - odometer translations: a homomorphism `Λ -> odometer`, which is trivial on
         the input by the new lemma.
     - So a genuinely relational phase field is needed, one whose solution space is
       itself minimal.

**Common core.** A minimal, relationally coupled field of hierarchy phases over a group
containing the input. This object is the G1(g) crux in every setting examined. It is
also where G1 meets G2, since rigidity must hold across the same coupling (lane
bh-g1-rigidsim).

## 4. Lessons for general BH (also on board/LESSONS.md)

1. The input group is invisible to every equicontinuous factor of the master-route SFT.
   Rigidity has to be proved in the fibers of that factor, not through an
   odometer or torus parse.
2. The non-amenable factor supplies grids for free. What remains of G1 is (M2) plus one
   minimality question, and in every setting that question is the diversification of a
   relationally coupled phase field.

## 5. Suggested next steps

- **G1-geom.** A minimal paradoxical SFT on a Kazhdan (or just non-amenable,
  non-residually-finite) group. Start by proving BSS's `F_2` claim for `M`, then try
  groups with many commuting or free subgroups.
- **Phase-field design.** Candidate couplings `R_s` given by "phases differ by a
  bounded carry", i.e. odometer relations that are not graphs. Test minimality of the
  solution space on `F_2 x F_2`, where everything is concrete.
- **Coordinate with G2.** If the phase field is rigid (a unique local extension of phases
  across grids), rigidity of the whole SFT may reduce to the fixed-point-tiling rigidity
  conjecture (G2-fp) inside each grid.
