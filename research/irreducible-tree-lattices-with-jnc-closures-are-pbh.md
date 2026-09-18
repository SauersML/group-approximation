---
rg: 2
id: irreducible-tree-lattices-with-jnc-closures-are-pbh
kind: claim
title: An irreducible lattice on a product of trees whose factor closures are just-non-compact acts faithfully on every factor, so it satisfies permutational Boone--Higman; three-tree lattices escape only through a non-just-non-compact closure
distinct_from:
  product-of-trees-lattices-with-faithful-factor-satisfy-pbh: that assumes a faithful or separating set of factors; this derives faithfulness on every factor from the Bader--Shalom normal subgroup theorem.
  tree-lattices-split-into-irreducible-blocks: that reduces every lattice to irreducible blocks; this settles the irreducible blocks whose factor closures are just-non-compact.
  boone-higman-via-bader-shalom-lattice-hosts: that uses Bader--Shalom lattices as hosts for arbitrary inputs; this uses the same theorem to put given tree lattices into the type (A) class.
---

**ESTABLISHED** through `irreducible-jnc-tree-lattices-pbh-via-bader-shalom`
(lane proof; not independently reviewed; no priority claimed). It rests on
`bader-shalom-normal-subgroup-theorem`, which is imported by citation.

**Setting.** As in `tree-lattices-split-into-irreducible-blocks`: `Γ <= Aut(X)` is
a cocompact lattice on `X = T_1 x ... x T_n`, `n >= 2`, each `T_i` leafless,
locally finite and with more than two ends; `Γ_0` preserves the factors.
`Ḡ_i` is the closure of `pr_i(Γ_0)` in `Aut(T_i)`.

1. **No abelian normal subgroups, no fixed ends.** If `Ḡ_i` is non-discrete, it
   fixes no end of `T_i` and has no nontrivial abelian normal subgroup.
2. **Irreducible case.** Suppose `Γ` is irreducible (no proper sub-product
   projection of `Γ_0` is discrete) and every `Ḡ_i` is just-non-compact (every
   nontrivial closed normal subgroup is cocompact). Then `Γ_0` is just-infinite,
   it acts faithfully on every `T_i`, and `Γ ∈ B_A`. So every subgroup of `Γ`
   embeds in a finitely presented simple group.
3. **General lattices.** Let `Γ_0` be virtually `Λ_1 x ... x Λ_r` as in item 2
   of `tree-lattices-split-into-irreducible-blocks`. If every block `Λ_s` on at
   least three trees has just-non-compact factor closures, then `Γ ∈ B_A`.
4. **Three trees.** A cocompact lattice on three leafless thick trees that is
   not in `B_A` must be irreducible, with some factor closure `Ḡ_i` that is
   non-discrete but not just-non-compact.

**When the hypothesis holds.** By `burger-mozes-infinitely-transitive-tree-groups`
item 2, a non-discrete locally quasiprimitive `Ḡ_i` has every nontrivial closed
normal subgroup either cocompact or discrete inside `QZ(Ḡ_i)`. So it is
just-non-compact whenever `QZ(Ḡ_i) = 1`, for instance when `Ḡ_i` is locally
`∞`-transitive (item 3 there). The local action of `Ḡ_i` at a vertex equals that
of `pr_i(Γ_0)`, so local quasiprimitivity can be read off the lattice.

**Scope.**
- Item 2 does not need residual finiteness and covers non-residually-finite
  irreducible lattices, provided their closures are just-non-compact.
- The open case of `product-of-trees-lattices-satisfy-permutational-boone-higman`
  for three trees is now exactly item 4. Nothing here constructs or excludes an
  irreducible three-tree lattice with a non-just-non-compact closure.
