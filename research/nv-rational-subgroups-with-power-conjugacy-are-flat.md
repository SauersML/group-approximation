---
rg: 2
id: nv-rational-subgroups-with-power-conjugacy-are-flat
kind: claim
title: A copy of Q in nV with one element conjugate to a proper power has zero exponents at all periodic points, so the landed copy of Q in 2V is never the translation group of Aff(Q)
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that constrains one element g with f g^k f^-1 = g^l; this transfers the constraint to every element of a rank-one divisible subgroup containing a power of g, and applies it to the landed copy of Q.
  rational-stepping-stones-in-nv-need-bs12-or-heisenberg: that shows an embedding of Aff(Q), SL_2(Q) or GL_n(Q) in nV forces BS(1,2) into nV; this says which copies of Q can carry the translations or root subgroups, and excludes the known one.
  rationals-embed-in-brin-thompson-group-2v: that constructs a copy R of Q in 2V; this shows no nontrivial element of R is conjugate in any nV to a proper power.
---

**ESTABLISHED** through `nv-rational-subgroups-with-power-conjugacy-are-flat-proof`.
Lane proof from the landed exponent-cocycle node; not independently reviewed. No
priority claimed.

**Notation.** `nV` acts on `C^n`, `C = {0,1}^N`. For `g ∈ nV` the exponent cocycle is
`δ_g(x) = (|v_j| - |u_j|)_j ∈ Z^n` on a table brick `Π C(u_j) -> Π C(v_j)` containing
`x`, as in `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`. Call
`g` **exponent-flat** if `δ_{g^q}(z) = 0` for every periodic point `z` of `g` of least
period `q`.

**Statement.** Let `n >= 1`.
1. **Flat transfer.** Let `D <= nV` be isomorphic to `(Q,+)`, or more generally
   torsion-free with every two nontrivial elements having a common nontrivial power.
   Suppose some `h ∈ D \ {1}` satisfies `f h f^-1 = h^m` for some `f ∈ nV` and some
   integer `m` with `|m| >= 2`. Then every element of `D \ {1}` is exponent-flat.
2. **Stepping stones.** Let `φ` be an injective homomorphism into `nV` from one of
   `Aff(Q) = Q ⋊ Q^x`, `B_k(Q)`, `SL_k(Q)`, `GL_k(Q)`, `PSL_k(Q)`, `PGL_k(Q)` (`k >= 2`).
   Then the image of the translation subgroup `{x ↦ x + b}` (for `Aff(Q)`) or of the
   root subgroup `{e_12(q)}` (otherwise) is an exponent-flat copy of `Q`. Here
   `t_1 ~ t_1^2` in `Aff(Q)` by the dilation `x ↦ 2x`, and `e_12(1) ~ e_12(4)` by
   `diag(2, 1/2, 1, …, 1)`, which lies in every group listed.
3. **The landed copy is excluded.** The copy `R = ∪_n ⟨s_n⟩ <= 2V` of
   `rationals-embed-in-brin-thompson-group-2v` (base `t`: `00w ↦ 0w`, `01w ↦ 10w`,
   `1w ↦ 11w`) contains `s_0 = t × id`. It fixes `(0^∞, y)` for every `y`, with
   `δ_{s_0}(0^∞, y) = (-1, 0)`. So `s_0` is not exponent-flat. By item 1, no element
   of `R \ {1}` is conjugate in any `nV` (`R <= 2V <= nV` on the first two
   coordinates) to a proper power of itself. By item 2, `R` is not the image of the
   translation subgroup or root subgroup under any embedding of the groups in item 2
   into any `nV`. The same holds for every copy of `Q` in `nV` containing an element
   with a periodic point of nonzero exponent. That includes the root tower of `g × id`
   for every `g ∈ V` that has a hyperbolic periodic point. By the still-uncited
   `infinite-order-elements-of-v-have-hyperbolic-periodic-points`, that would be every
   infinite-order `g`.

**What this changes.** The only proved divisible subgroup of an `nV` on main cannot
serve any rational stepping stone of `gl-n-q-embeds-in-fp-simple-group`. An `nV` host
needs a new, exponent-flat copy of `Q` whose elements are, moreover,
`BS(1,m)` witnesses for every `m`. By items 2–3 of
`bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`, each nontrivial
element then has an open periodic set and a nonempty aperiodic core. Such a copy of
`Q` does exist in `3V`, with no periodic points at all:
`three-v-contains-aperiodic-rationals`. Whether any of its elements is conjugate to a
proper power is open.
