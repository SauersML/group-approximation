---
rg: 2
id: fp-simple-group-of-finite-cohomological-dimension-above-two
kind: claim
title: There is a finitely presented infinite simple group of finite cohomological dimension greater than 2 (Kourovka 21.46)
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-cd3-sources.md
  - research/artifacts/gq-bh-bh-free-42-al-scaffolding-reading.md
---

**OPEN.**

## Source

- **Kourovka Notebook, 21st issue, Problem 21.46** (F. Fournier-Facio), marked "Well-known problem"
  (`gq/src/kourovka/21tkt.tex`, l.13681). It asks whether some finitely presented (infinite) simple
  group has finite cohomological dimension greater than 2.
- **Amir–Lazarovich, arXiv:2605.09493, Discussion (l.2386–2407).** They say every known finitely
  presented simple group has cd 2 or ∞, and ask whether other values occur.
- **Examples of each value.**
  - cd 2: torsion-free simple lattices in products of two trees, from Burger–Mozes on.
  - cd ∞: finitely presented simple groups with torsion, such as Thompson's T and V.

## Attempts

The normal-subgroup-theorem route builds a simple group as the finite residual Λ of an irreducible,
just-infinite, non-residually-finite lattice Λ'. Such Λ is torsion-free, so of cd = dim, only if
the torsion of Λ' dies in the finite quotient Λ'/Λ.

- **RSV doubles are dead.** Rungtanapirom–Stix–Vdovina, arXiv:1808.03290, give non-residually-finite
  lattices on products of d ≥ 3 trees.
  - `rsv-quaternionic-doubles-are-never-virtually-simple` shows they are never virtually simple.
  - A second proof: projecting `Y ⊠_{□^d} Y → Y` onto one factor gives `π_1 D(X) ↠ Γ`. The kernel
    is nontrivial because Γ is residually finite and `π_1 D(X)` is not.
- **Amir–Lazarovich lattices on `T_c × X_{O_d}` (dim 3) are dead for the known seeds.**
  - `amir-lazarovich-lattice-torsion-is-square-diagonals`: the torsion of `Λ'^+` is conjugate to
    the square diagonals `DD'`.
  - `amir-lazarovich-simple-lattice-has-torsion-iff-index-four`: all `DD'` are conjugate, and
    `Λ` has torsion iff `Λ = Λ'^+`.
  - `amir-lazarovich-plus-subgroup-is-perfect`: `Λ'^+` is perfect for every BMW seed. So a
    torsion-free Λ needs a nonabelian finite simple quotient of `Λ'^+`.
  - `amir-lazarovich-simple-lattices-have-torsion` (bh-free-extensions): for AL's explicit scaffolding
    (d ≥ 9), and for seeds with a collapsed pair `a_j a_k ∈ FR(Γ)`, `Λ = Λ'^+` has torsion. This
    covers both sources AL cite for their seeds.
- **Size.** Every AL instance with AL's `υ`'s has `d >= 9`, since scaffolding axiom (E4) forces it,
  so `|V(O_d)| >= 24310` (artifact `gq-bh-bh-free-42-al-scaffolding-reading.md`, §B).

## What is left

- **(a) AL data with an exotic seed.** Needed: an involutive, non-residually-finite BMW group Γ
  with alternating local actions, and `Γ/FR(Γ)` separating all of `a_1, …, a_n`. Then a nonabelian
  finite simple quotient of `Λ'^+` would still be required, and no candidate is known.
- **(b) Seeds without involutions.** The torsion comes from the involutive square data: every
  generator is an involution, so every square gives a diagonal involution `DD'`. Two options avoid
  it:
  - a construction on `T × X` that is torsion-free from the start;
  - a torsion-free seed, where Radu embeds his torsion-free `Γ_{4,4}` into larger (d_1,d_2)-groups.

  bh-free-extensions records a parity constraint for one-vertex square complexes with link `O_d`.
- **(c) Three or more trees.** Such a lattice needs a non-residually-finite irreducible lattice with
  NST-type local actions. The smallest case is excluded by Radu, arXiv:1712.01091, Main Theorem on
  three trees (l.321), whose proof is a GAP computation over his (6,6)-group census. On
  `T_6 × T_6 × T_6` there is no vertex-simply-transitive Γ with all of the following:
  - non-discrete projections, with local actions `>= Alt(6)`;
  - dense projections to `H_1 × H_3` and to `H_2 × H_3`;
  - torsion-free stabilizers `Γ(v_1, v_3)` and `Γ(v_2, v_3)`.

  That last hypothesis is exactly the torsion-free regime that 21.46 needs.

## Lesson for general BH

- **Torsion versus simplicity.** In every NST construction the torsion and the simplicity come from
  the same involutive square data. The colour-preserving subgroup is perfect, and it is usually
  simple. Its involutions `DD'` survive into the simple group.
- **What cd > 2 needs.** A finitely presented simple group of finite cd > 2 needs non-residual
  finiteness that is built from torsion-free local data. Transitive local actions alone will not
  kill the torsion.
- **For BH.** Hosts obtained this way have cd ∞, which is harmless for BH. But finite-dimensional
  simple hosts are not available from these constructions. So a BH proof cannot ask its fp simple
  hosts to have finite cd, or asphericity, unless it supplies a new source of torsion-free
  non-residually-finite lattices.
