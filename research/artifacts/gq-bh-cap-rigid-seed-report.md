# CAP for rigid seeds: state of the question (09-18 ~17:00)

Lane bh-star-a, assigned the rigid version of v6's top gate CAP (b5ad39956):
> Do word problems of finitely presented groups with a quantum-rigid seed lie in one complexity class?

**Status.** Nothing here is reviewed.
- **Not decided.** No general bound is proved, and no rigid seed over a group with hard word problem is
  built.
- **What is proved.** A splitting of the question, new members of `𝒞`, and a list of neutral
  mechanisms.

## 1. What other lanes established (credit)

- **bh-invent-15.**
  - `seeded-groups-have-solvable-word-problem` (a9187d6d4): a seed alone forces solvable WP, with no
    rigidity (Jeandel's method, localized to the seed cylinder).
  - CAP is exactly a uniform bound on the seed-collapse function `κ(n)`.
  - `seeds-never-survive-marked-approximation` (c90fc9348): no approximation argument can decide
    CAP, so any CAP argument is non-local.
- **bh-g1-universal-point.** `bs12-rigid-seed-is-its-normal-form` (f6aedfd93): an explicit 6-letter
  rigid seed on BS(1,2).
  - It is forced at linear radius despite exponential distortion.
  - The tree layer of every locally finite splitting seed is Britton's normal form, so it is
    complexity-neutral.
- **bh-invent-11.** `compiled-hnn-stages-are-capped-inside-brin-thompson-groups` (5ecd29e1b4, after
  c0dfc4ce5 and c4710d9ab).
  - In-host compilers exist.
  - Every finitely generated subgroup of every nV has coNP word problem, so compilation inside
    Brin–Thompson hosts is capped.
- **bh-free-56 (rung 1c).**
  - Relative seeds whose stabilizer contains a normal N descend to Λ/N, so Mihailova towers only
    relocate CAP into a two-sided seed on the quotient.
  - The open rung is core-free machine subgroups (Aanderaa–Cohen).
- **bh-g2-buildings and bh-synth-lead.** The definitions, tree gluing (bf61de7d0), and the formulation of
  CAP.

## 2. What this lane adds

1. **`quantum-rigidity-passes-to-subshifts`.**
   - Rigidity is monotone under inclusion. So a rigid seed is exactly a seed carved by local rules out of
     any rigid ambient SFT.
   - Deterministic finite-fibre extensions (`deterministic-extensions-of-rigid-sfts-are-rigid`) give
     rigid ambients for free, but they are finite-state relative to their base. They cannot raise `κ`.
   - A cellular-automaton space-time layer reads neighbouring fibre letters. So it is **not** such an
     extension, and its rigidity is v6 gate 4, not a closure theorem.
2. **`torsion-free-tree-product-lattices-lie-in-the-rigid-seed-class`.**
   - Every torsion-free cocompact lattice on a product of locally finite trees is in `𝒞`. The seed is a
     vertex tuple, rigid by coupling and carved to one orbit by block rules, and (S5) holds.
   - This includes the Burger–Mozes simple groups, the first infinite simple members of `𝒞`, and Wise's
     non-residually-finite lattices.
   - All of them are CAT(0), with word problem in NP.
3. **Census.** Every group recorded in `𝒞` as of this writing (to this lane's knowledge) has word problem
   in EXP:
   - finite groups, `Z`, BS(1,2) (in P);
   - tree-product lattices (in NP);
   - closure under free and direct products, which is polynomial-time reducible to the factors.

   So CAP is **untested** by every recorded member. Rungs 1a, 1b and 1d all have word problem in NP or
   better: BS(1,2) and H₃(Z) in P, and Ã₂ lattices in NP (CAT(0)).

## 3. The splitting of CAP

- **A rigid seed has two parts.** It is (a) a rigid ambient SFT over `Λ` and (b) a seed carved inside it.
  Step (b) never costs rigidity.
- **Ambient-builders known.** Compression codings (trees, products, coupled joins), deterministic
  finite-fibre extensions, Ã₂ boundary skew shifts, and products. Each is complexity-neutral relative to
  its input:
  - normal forms, for trees and splittings;
  - finite transducers, for deterministic layers;
  - CAT(0) geometry, for buildings and tree products.
- **So ¬CAP needs** a rigid ambient whose local rules already encode computation at the seed. That is
  programmable rigidity (v6 gate 4) placed at an origin. Concretely:
  - (i) a rigid SFT with a deterministic machine layer that is **not** finite-fibre over its base, e.g. a
    reversible or permutive computation reading neighbouring cells;
  - (ii) carved to a seed whose collapse function `κ` grows like the machine's time.
- **A CAP theorem needs** a bound on what rigid ambients can carry. The carving step is free, and by
  c90fc9348 the bound cannot be local.

## 4. Recommended next steps

- **For ¬CAP (rung 1c, bh-free-56 / bh-invent-03).** Look for a computation layer that is rigid by its
  own determinism: reversible, and permutive in enough directions, as in
  `permutive-triangle-sfts-are-quantum-rigid`. Couple it to a compression base, then carve the seed.
  The deterministic-extension closure does not cover this, because the layer reads neighbouring cells.
  Check (S3) first: rogue computations over boundary points must be limits of translates of the seed.
- **For CAP.** Try to prove that every rigid SFT over a finitely presented group is a finite-fibre
  extension of a compression coding. That is a structure theorem for rigidity; its failure would locate
  ¬CAP.
