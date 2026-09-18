---
rg: 2
id: haagerup-hosts-carry-no-weak-expander
kind: claim
title: No finitely generated subgroup of a Haagerup group carries a weakly embedded expander, so expander-type non-exact witnesses cannot live inside V, T, F or an SFT full group
distinct_from:
  thompson-v-has-haagerup-property: that imports a proper affine action for V and deduces that Kazhdan subgroups are finite; this proves that the same action forbids every weakly embedded expander in every finitely generated subgroup, which excludes a-T-menable-free witnesses of non-exactness such as Sapir's group, not only Kazhdan ones.
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's a-T-menability import; this is the coarse-geometric consequence for non-exact subgroups, which that node does not state.
  fp-simple-nonexact-group: that asks for one finitely presented simple non-exact group; this shows which hosts cannot contain the known kind of witness, and names the one known finitely presented simple host that escapes.
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that turns exactness into a Boone--Higman separator; this kills the Haagerup hosts as places to look for an expander-type counterexample to the separator's hypothesis.
artifacts:
  - research/haagerup-hosts-carry-no-weak-expander-proof.md
---

**ESTABLISHED.** Say that a finitely generated group `M`, with a word metric,
*carries a weakly embedded expander* if there are

- finite connected graphs `X_n` with degree at most `d`, `|X_n| → ∞`, and
  spectral gap `λ_1(X_n) ≥ λ > 0` of the combinatorial Laplacian, and
- maps `f_n : X_n → M` with `d_M(f_n x, f_n y) ≤ L` for every edge `xy`, and
  maximal fibre `s_n = max_m |f_n^{-1}(m)|` satisfying `s_n / |X_n| → 0`.

**Theorem.** If a countable group `G` has the Haagerup property, then no
finitely generated subgroup of `G` carries a weakly embedded expander.

The proof is `haagerup-hosts-carry-no-weak-expander-proof`. It has two steps:

1. A proper cocycle is a coarse embedding into Hilbert space.
2. The expander Poincaré inequality forces half of all pairs of `X_n` into a
   bounded `M`-ball, and small fibres forbid that.

## Hosts to which it applies

Every subgroup of each of the following groups:

- Thompson's groups `F ≤ T ≤ V`, by `thompson-v-has-haagerup-property`;
- the topological full group of every one-sided irreducible shift of finite
  type, including all Higman--Thompson groups `V_{n,r}`, by
  `sft-topological-full-groups-have-the-haagerup-property`.

Hughes (arXiv:0804.0610) extends the list to his locally finitely determined
groups of local similarities of compact ultrametric spaces. This is recorded
as a pointer and is not load-bearing here.

## The class of approaches this kills

**The approaches.** Produce a finitely presented simple non-exact group by
embedding a known *expander-type* non-exact group `M` into one of the hosts
above, or into any other Haagerup group. Expander-type means that `M` coarsely
contains an expander, as Sapir's finitely presented group (arXiv:1103.3873)
and the Gromov--Arzhantseva--Delzant--Osajda monsters do, or more generally
that `M` carries a weakly embedded expander.

**The invariant.** A proper conditionally negative definite function on the
host. It restricts to every subgroup and gives a coarse embedding of each
finitely generated one.

**Where every member dies.** At the counting step, §2 of the proof. The
Poincaré inequality puts half of all `|X_n|^2` pairs within a bounded
`M`-distance `R`. There are at most `|X_n| · |B_M(R)| · s_n = o(|X_n|^2)` such
pairs.

What survives in these hosts is only a non-exact subgroup that is itself
a-T-menable, of Arzhantseva--Osajda type. No finitely presented such subgroup
of `V` is known.

## The finitely presented simple host that escapes

The binary Leavitt unit group `L^x = L_{F_2}(1,2)^x` is finitely presented
and simple (`fp-simple-nonsofic-group`). It is **not** Haagerup, for three
reasons:

- by `char-two-laurent-linear-groups-satisfy-boone-higman`, it contains every
  finitely generated subgroup of `GL_3(F_2<x,y>)`, hence `EL_3(F_2<x,y>)`;
- `EL_3(F_2<x,y>)` has property (T), by
  `elementary-group-property-t-over-free-algebras` (Ershov--Jaikin-Zapirain,
  arXiv:0809.4095: "we prove property (T) for the groups EL_n(R), where n≥3
  and R is an arbitrary finitely generated associative ring");
- `EL_3(F_2<x,y>)` is infinite, since it surjects onto the infinite group
  `EL_3(F_2[x])`.

So the theorem does not block `L^x`. That is why the open lane
`fp-simple-nonexact-group-via-free-algebra-linear-groups` runs through `L^x`
and not through the Thompson family.

DERIVATION
haagerup-hosts-carry-no-weak-expander-proof
