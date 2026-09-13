---
rg: 2
id: linf-preserving-proper-actions-give-contractible-rips
kind: claim
title: A group acting properly on R^n by signed-permutation affine maps that include the lattice translations has a contractible Rips complex
distinct_from:
  contractible-rips-groups-closed-under-direct-products: that builds contractible Rips complexes of direct products from their factors; this covers crystallographic groups with nontrivial holonomy and glide or screw translations, which are not direct products
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n with the l^1 generators; this uses an l^infinity generating set and allows any virtually abelian group whose point group is monomial with signs
  virtually-abelian-groups-have-contractible-rips-complexes: that gives existence for every virtually abelian group through Zaremsky's orbit theorem, with no explicit scale; this is a self-contained dominated-vertex proof with explicit l^infinity generating sets and every scale c >= 4, for signed-permutation point groups
---

**ESTABLISHED** (route `linf-preserving-proper-actions-give-contractible-rips-proof`).

Let `e_1, ..., e_n` be a basis of `R^n` and `‖x‖_∞ = max_i |x_i|` for
`x = Σ x_i e_i`. Let a group `G` act on `R^n` by affine maps `g x = A_g x + t_g`
such that:

1. the action is properly discontinuous: for every compact `C ⊆ R^n` only finitely
   many `g` satisfy `gC ∩ C ≠ ∅`;
2. every linear part `A_g` permutes the set `{±e_1, ..., ±e_n}`;
3. for each `i`, the translation `x ↦ x + e_i` is the action of some element of `G`.

Then for every `x_0 ∈ R^n` and every `c >= 4`, the set
`S_c = {g ∈ G ∖ {1} : ‖g x_0 − x_0‖_∞ <= c}` is a finite symmetric generating set
of `G`, and the Rips complex `P_1(G, S_c)` is contractible.

The kernel of the action is finite, since it fixes `x_0`. So the theorem applies
to every group with a finite normal subgroup whose quotient acts in this way.

**Examples.**

- `Z^n × F` with `F` finite, acting through the projection to `Z^n`. Li–Sánchez
  Saldaña (arXiv:2608.24279, Theorem 1.6) prove more for this case: type R for the
  standard generators together with any generating set of `F`.
- The Klein bottle group `⟨a, b | b a b^-1 = a^-1⟩`, acting on `R^2` by
  `a(x,y) = (x+1, y)` and `b(x,y) = (−x, y + 1/2)`. Here `e_1` and `e_2` are the
  translations `a` and `b^2`, and the linear parts are `diag(±1, 1)`. Its holonomy
  is nontrivial and it is not a direct product.
- Every crystallographic group whose point group, in some basis of the rational
  span of its translation lattice, consists of signed permutation matrices. Take
  `e_i` to be integer multiples of that basis lying in the lattice. In dimension 3
  this includes the space groups of the triclinic, monoclinic, orthorhombic,
  tetragonal and cubic systems, in their conventional axes, including those with
  screw axes, glide planes and centred lattices. Trigonal and hexagonal space
  groups are not covered.

For Zaremsky Problem 4.1: all of these groups are amenable and automatic, so they
are positive cases of `amenable-automatic-groups-have-contractible-rips-complexes`.
Torsion-free ones (Bieberbach groups, such as the Klein bottle group) are of type F,
so they are positive cases for Problem 4.7 as well.
