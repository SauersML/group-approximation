---
rg: 2
id: reducible-euclidean-building-lattices-lie-in-type-a-class
kind: claim
title: Every cocompact lattice on a finite product of locally finite thick Euclidean buildings and trees lies in the type (A) class, irreducible lattices and torsion included
distinct_from:
  euclidean-building-lattices-lie-in-permutational-bh-class: that covers irreducible buildings, and products only through commensurability with products of lattices; this covers every cocompact lattice on a reducible building, including irreducible lattices in products.
  cocompact-tree-product-lattices-lie-in-type-a-class: that is the case where every factor is a tree.
---

**ESTABLISHED** through `reducible-building-lattices-via-product-boxes` (lane proof;
not independently reviewed; no priority claimed).

**Statement.** Let `X = X_1 x ... x X_m`, where each `X_i` is a locally finite thick
irreducible Euclidean building or a locally finite leafless tree with more than two
ends. Let `Γ ≤ Aut(X)` be discrete and cocompact; factors may be permuted, and `Γ`
may have torsion. Then `Γ ∈ B_A`, so every subgroup of `Γ` embeds in a finitely
presented simple group.

**Covered.** Irreducible lattices in products of exotic Ã₂, C̃₂ or G̃₂ buildings with
each other or with trees, and all the one-factor cases.

**Lesson for general BH.** Finite codings of boundaries multiply. The orbit category
of a lattice in a product is built from the factor codings. Its pieces are strongly
connected as soon as each factor's coding has no transient classes, and complete
reducibility by counting gives exactly that. Effectiveness holds factorwise by
Lemma H (`automorphisms-fixing-open-boundary-sets-fix-large-balls`), with no
discreteness in the factors. So the coded-host machine
(`finitely-coded-cantor-actions-give-type-a-hosts`) is closed under taking lattices
in products. Irreducibility of the lattice, arithmeticity, residual finiteness and
normal subgroup theorems play no role.
