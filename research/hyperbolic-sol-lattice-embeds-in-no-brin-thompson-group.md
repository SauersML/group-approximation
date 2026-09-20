---
rg: 2
id: hyperbolic-sol-lattice-embeds-in-no-brin-thompson-group
kind: claim
title: No Sol lattice Z^2 ⋊_A Z with A ∈ GL_2(Z) hyperbolic embeds in any Brin-Thompson group nV
distinct_from:
  heisenberg-group-embeds-in-no-brin-thompson-group: that excludes the unipotent subgroup H_3(Z) of SL_3(Z); this excludes the hyperbolic (Cartan-type) subgroup Z^2 ⋊_A Z of SL_3(Z). Both give GL_3(Z) in no nV, but they are independent, and the obstructions known for this one (free locus, coordinate shadows) have no Heisenberg analogue.
  every-gl-n-z-embeds-in-some-brin-thompson-group: that is the opposite direction for all GL_n(Z); a yes here refutes it at n = 3.
  distorted-z2-with-hyperbolic-normalizer-in-nv-has-a-free-locus: that is the ESTABLISHED necessary condition (clopen fixed sets and a nonempty closed free locus of the base); this is the full non-embedding statement it points at.
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that kills the block-split and finite-shadow bases; this asks for all bases.
  brin-thompson-2v-is-not-a-t-menable: that looks for a relative-(T) witness in 2V; every Burger-pair witness Z^2 ⋊ Γ contains a hyperbolic Sol lattice, so a yes here kills all of them.
---

**Statement.** For every `n >= 1` and every hyperbolic `A ∈ GL_2(Z)` (a real eigenvalue of
absolute value `> 1`), the group `Z^2 ⋊_A Z` is not isomorphic to a subgroup of `nV`. The case
`n = 1` is already known: `Z^2` is exponentially distorted in the Sol lattice, but cyclic subgroups
of `V` are undistorted.

**Why it is a gate.**
- *GL_3(Z).* The matrices `[[A^k, v], [0, 1]]` with `A = [[2,1],[1,1]]` form `Z^2 ⋊_A Z ≤ SL_3(Z)`.
  So a yes here gives `some-gl-n-z-embeds-in-no-brin-thompson-group` at `n = 3`, by
  `some-gl-n-z-in-no-nv-via-sol`. This route is independent of the Heisenberg route.
- *Burger pairs.* A non-amenable `Γ ≤ GL_2(Z)` contains a hyperbolic `A`, so `Z^2 ⋊ Γ` contains
  `Z^2 ⋊_A Z`. A yes here removes every Burger-pair witness for
  `brin-thompson-2v-is-not-a-t-menable`, in every `nV`.

**Necessary conditions already ESTABLISHED.** A counterexample `⟨H, g⟩ ≅ Z^2 ⋊_A Z ≤ nV` must meet
all of the following.
- The base `H` is drift-free in every direction, and every periodic point of every `x^v` has zero
  offset.
- `Fix(x^v)` is clopen, and `H` acts freely on a nonempty closed invariant set `W`. `W` carries an
  invariant probability measure, and rank-one stabilizers are null for every invariant measure
  (`distorted-z2-with-hyperbolic-normalizer-in-nv-has-a-free-locus`).
- `H` is coordinate-mixing: every shadow set `D_J` is empty or infinite
  (`coordinate-shadows-rigidify-abelian-normalizers-in-nv`).
- `⟨H, g⟩` lies in no fibred `V`-tower, since it has a distorted element
  (`fibred-v-towers-in-brin-thompson-groups-are-distortion-free`).

## Attempts

- 2026-09-20 (swarm-0917-w23-w23-nv-pull, unreviewed): **four constructions die; none reaches a
  hyperbolic `A`.**
  - *Locally non-free bases* (disjoint supports; piecewise rigid-stabilizer bases). They die at the
    free-locus theorem (F3). The stabilizer lines would form a finite `A`-invariant set of rational
    lines.
  - *Block-split bases* (products of SMART odometers, compiler products). They die at (S6): only
    monomial twisting matrices are realizable.
  - *Two-code trick.* Put two dilation codes on one `Z^2`, for commuting diagonal `M, M'` of equal
    determinant, so that `g g'^{-1}` realizes `M^{-1}M'`. For a hyperbolic target this requires
    `M^{-1}M'` to be hyperbolic, hence non-diagonal in the given basis.
    - Over a block-split base, it dies at (S6). Example: eigenvalues `√3` and `2√3 − 3` are
      non-monomial.
    - Over a minimal odometer base, the second code must already be an element of `kV` twisting by
      `A`, which is circular.
  - *Compiler twists.* Over their own base, the dilation groups of
    `monomial-renormalization-compiler-gives-dilation-groups-in-nv` twist by monomial matrices. A
    monomial `2 × 2` matrix has a diagonal square, which fixes a rational line. By Step 0 of
    `distorted-z2-free-locus-proof`, no power of a hyperbolic `A` does. This is weaker than (S6):
    it rules out the compiler's own base, not every `Z^2` inside a compiler group.
  - *Finite-window symbolic models* (the base acting through a bounded window on a subshift
    coordinate). These generate locally finite groups, so they contain no `Z^2`.
  - **Still open.** A coordinate-mixing base that acts freely on some nonempty closed set. The
    natural candidate is a `Z^2`-odometer (a `Z^2` action by adding machines on `C^n`) with a
    hyperbolic automorphism. Its free locus is automatic. Any obstruction would have to set the
    finiteness of `nV`-germs against the irrational expansion rate `λ`. This is analogous to the
    arithmetic gate at the prime `2` in `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`,
    which is also still open.
