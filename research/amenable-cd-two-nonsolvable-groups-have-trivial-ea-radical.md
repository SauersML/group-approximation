---
rg: 2
id: amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
kind: claim
title: A finitely generated amenable group of cd 2 with a nontrivial elementary amenable normal subgroup or a commensurated infinite cyclic subgroup is BS(1,m)
distinct_from:
  amenable-fp-iff-affiliated-top-homology-vanishes: that shows a two-dimensional counterexample is exactly a non-FP_2 group with H_1(G;U(G)) nonzero; this shows such a group has no elementary amenable normal subgroup and no commensurated cyclic subgroup, a structural constraint that dimension counting does not see
  amenable-cd-two-solvable-iff-coherent-rational-group-algebra: that characterises the solvable groups ring-theoretically; this proves solvability for a subgroup-theoretic class
  hillman-linnell-finite-hirsch-length-theorem: that is the elementary amenable case of the whole question; this uses it for a normal subgroup and then needs a splitting theorem to reach the whole group
  bieri-strebel-splitting-over-kernel-of-map-to-z: that splits finitely presented groups over kernels of characters; item 3 here records the finitely generated analogue that a two-dimensional counterexample can actually use, and what it does not give
---

**ESTABLISHED** through `amenable-cd-two-ea-radical-via-commensurated-cyclic-splitting`, from cited
theorems (Hillman--Linnell, Gildenhuys--Strebel, Kropholler 1990 / Margolis, the tree alternative
for amenable groups).

Let `G` be a finitely generated amenable group with `cd_Z G = 2`.

1. **Commensurated cyclic subgroup.** If `G` has a commensurated infinite cyclic subgroup `H`
   (`H ∩ gHg^-1` has finite index in `H` for all `g`), then `G` is virtually solvable, hence
   `G ≅ BS(1,m)` for some `m != 0`.
2. **Elementary amenable radical.** If `G` has a nontrivial elementary amenable normal subgroup,
   then `G ≅ BS(1,m)` for some `m != 0`.
3. **Descent along Σ¹ (only when Σ¹ supplies it).** If `G` is not solvable and is an ascending
   HNN extension `K*_φ` with finitely generated base `K` (for finitely generated `G` this happens
   exactly when some discrete character `χ` has `χ` or `−χ` in the BNS invariant `Σ¹(G)`), then
   `K` is again finitely generated, amenable, of cd 2 and not solvable.

**Consequence for Kropholler's question in dimension 2.** A finitely generated amenable
counterexample `G` of cd 2 (equivalently, by `amenable-fp-iff-affiliated-top-homology-vanishes`, a
fg amenable cd-2 group with `H_1(G; U(G)) != 0`):

- has trivial elementary amenable radical. In particular it has trivial centre and no nontrivial
  abelian normal subgroup;
- has no commensurated infinite cyclic subgroup;
- has only non-elementary-amenable nontrivial normal subgroups, all of cd exactly 2 (a normal
  subgroup of cd at most 1 is locally free and amenable, hence locally cyclic);
- is torsion-free with `Z[G]` not a domain (`amenable-cd-two-solvable-iff-coherent-rational-group-algebra`).

So a two-dimensional counterexample cannot be an extension with a nontrivial elementary amenable
kernel (in particular not a central extension, and not an extension of a group by `Z`, `Q`,
`Z²` or `BS(1,m)`), and none of its cyclic subgroups is commensurated. Any construction must be
"EA-simple" in this sense.

**What item 3 does not give.** The finitely presented Bieri--Strebel dichotomy `Σ¹ ∪ −Σ¹ = S(G)`
for groups without free subgroups fails for finitely generated groups that are not finitely
presented. The calibration example is `Z≀Z`: it is amenable and neither `±χ` for the top character
lies in `Σ¹`. A counterexample is not `FP_2`, so nothing forces it to split as an ascending HNN
extension over a finitely generated base. Descent needs a `Σ¹` input that a counterexample does
not supply.
