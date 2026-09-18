---
rg: 2
id: non-elementary-hyperbolic-groups-are-contracting-rsgs
kind: claim
title: Every non-elementary hyperbolic group is isomorphic to a contracting rational similarity group (BBMZ-hyperbolic Question 1.1)
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that is the established embedding of every hyperbolic group into a contracting RSG; this asks for an isomorphism with no free factor added.
  free-products-with-a-finite-factor-are-contracting-rsgs: that is the case of a finite free factor, established; this is the whole question.
  free-products-of-hyperbolic-groups-are-contracting-rsgs: that is the freely decomposable case, established; this is the whole question.
  virtually-free-product-hyperbolic-groups-are-contracting-rsgs: that is the virtually freely decomposable case, established; this is the whole question.
  contracting-rsgs-closed-under-products-with-finite-groups: that is a closure lemma used for the known cases; this is the question itself.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**OPEN.** This is Question 1.1 of Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy
the Boone--Higman conjecture*, arXiv:2309.06224v3 (§1, `ssec:open`, read in the TeX):
"Is every non-elementary hyperbolic group isomorphic to a contracting RSG?"

## Known cases (on main)

- **`G * Z`** for every hyperbolic `G` (BBMZ `thrm:FreeProductBoundary` together with
  `thrm:contracting`; BBMZ state this as "if `G` has `Z` as a proper free factor then the RSG
  is contracting").
- **`A * B`** for any two nontrivial hyperbolic groups, not both of order 2:
  `free-products-of-hyperbolic-groups-are-contracting-rsgs`, a lane proof. It generalizes
  both the `G * Z` case and the finite-factor case
  `free-products-with-a-finite-factor-are-contracting-rsgs`. So every freely decomposable
  non-elementary hyperbolic group is covered.
- **Finite-index overgroups** of any of the above:
  `contracting-rsgs-closed-under-finite-index-overgroups`, a lane proof (induced action). In
  particular `virtually-free-product-hyperbolic-groups-are-contracting-rsgs`: every
  non-elementary virtually free group, such as `SL_2(Z)` and `GL_2(Z)`, and every virtually
  torsion-free hyperbolic group with infinitely many ends. Direct products with finite groups,
  such as `F_2 × Z/2`, are the special case `contracting-rsgs-closed-under-products-with-finite-groups`.

## What remains

By the finite-index closure, `G` is covered as soon as one finite-index subgroup is. What
remains:
- **one-ended hyperbolic groups** (closed surface groups, closed hyperbolic 3-manifold groups,
  Kazhdan hyperbolic groups), where no finite-index subgroup splits freely; and
- **infinitely-ended hyperbolic groups none of whose finite-index subgroups splits freely.** Any
  such group is not virtually torsion-free, and whether such hyperbolic groups exist is open.

## Attempts

1. **2026-09-18 (lane `bh-free-23`).** The two BBMZ obstacles, re-examined.
   - (i) Finite normal subgroups: not intrinsic. Contracting RSGs can have nontrivial finite
     centers (`V_{Γ,E} × Z/2`). For direct products `H × N` with `N` finite, relabelled copies
     of the address space realize `N` faithfully. For a generating set not closed under `N`,
     even the horofunction boundary can see `N`. For example, `F_2 × Z/2` with generating set
     `{a, b, c}` has `∂_h ≅ ∂F_2 × {0,1}`, and `c` swaps the two copies.
   - (ii) Irreducible core: for every free splitting `A * B`, the shadows of points just past
     a syllable change have a single type, and translating a factor branch into such a shadow
     copies every atom type (`free-products-of-hyperbolic-groups-are-contracting-rsgs`). So
     obstacle (ii) disappears for all freely decomposable groups. For one-ended groups there is
     no cut vertex, and a new mechanism is needed.
   - A proposal, not attempted: for a finite normal subgroup `N` that is not a direct factor,
     look for a continuous `N`-valued cocycle on the germ groupoid of `G/N ↷ ∂_h(G/N)` that
     realizes the extension. `G` would then act on `∂_h(G/N) × N` by a skew product, and the
     finite-product construction would apply to that skew product.
2. **2026-09-18 (lane `bh-free-23`), the one-ended case.**
   - **Reduction.** By `contracting-rsgs-closed-under-finite-index-overgroups`, it is enough to
     realize one finite-index subgroup. For closed surface groups every finite-index subgroup is
     again a closed surface group, so a genuinely one-ended mechanism is needed.
   - **Markov codings already give RSG moves.** Let a Fuchsian group `Γ` act on `S^1` with a
     Bowen--Series-type Markov map `T`, such that `T|_{I_a} = g_a ∈ Γ` on each Markov interval.
     Blow up a countable invariant set to get a Cantor model, and code points by their
     `T`-itineraries. Then `T^{|α|}` restricted to the cylinder `C_α` is one group element `g_α`,
     and `g_α(αω) = ω`. So `g_β^{-1} g_α` maps `C_α` onto `C_β` by the canonical similarity
     whenever `t(α) = t(β)`. That is the RSG condition, with no hyperbolic-group geometry.
   - **What is unverified:**
     - rationality of the generators at the blown-up points;
     - finiteness of the nucleus (the analogue of the BBMZ contracting lemma);
     - irreducibility of the transition graph, which is expected from topological mixing of the
       Bowen--Series map.

     Bowen--Series (Publ. IHES 50, 1979) was not read at source. The nucleus cannot consist only
     of identity maps unless the surface group embeds in `V_{Γ,E}`, which is not known (compare
     survey Question 4.7). So a proof should expect to control non-identity local actions
     `g_β s g_α^{-1}`.
