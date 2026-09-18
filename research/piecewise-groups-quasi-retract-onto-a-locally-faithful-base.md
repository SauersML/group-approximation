---
rg: 2
id: piecewise-groups-quasi-retract-onto-a-locally-faithful-base
kind: claim
title: A finitely generated group of H-piecewise homeomorphisms containing H quasi-retracts onto H as soon as H is locally faithful at one point, so type F_n, type FP_n and Dehn function bounds pass down to H
requires:
  - quasi-retracts-have-smaller-dehn-functions
distinct_from:
  full-group-label-length-bounds-distortion: that bounds label length and so gives undistortion of H; this gives a coarse Lipschitz RETRACTION onto H (the label at one point), which carries finiteness properties, not only distances.
  twisted-brin-thompson-groups-quasi-retract-onto-acting-group: that is the Belk--Zaremsky retraction SV_G -> G for twisted Brin--Thompson groups; this is the same germinal idea for groups whose labels lie in a subgroup H, with H locally faithful at one point.
  fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups: that shows fp hosts have fp germ groups at the finitely many singular points of a finite-singularity extension; this has no singular set at all, every element being piecewise in H, and concludes that H itself inherits the finiteness of the host.
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary apart from Alonso's
theorem; not reviewed). No priority is claimed: the retraction is the germinal-twist idea of
Belk--Zaremsky and of FFWZ Proposition 4.17, applied to a subgroup of labels.

## Setting

`X` is a compact space and `H <= Homeo(X)` a finitely generated group.
- `[[H | X]]` is the group of homeomorphisms of `X` that locally agree with elements of `H`.
  By compactness each `k` in it has a finite open cover `U_1, ..., U_m` of `X` and labels
  `h_i ∈ H` with `k = h_i` on `U_i`.
- `H` is **locally faithful at `κ ∈ X`** if no nontrivial element of `H` is the identity on
  a neighbourhood of `κ`.

## Theorem

Let `K` be finitely generated with `H <= K <= [[H | X]]`, and let `H` be locally faithful at
some point `κ`. Then `H` is a quasi-retract of `K`. Consequently (Alonso, as imported in
`quasi-retracts-have-smaller-dehn-functions`):
1. if `K` is of type `F_n`, or `FP_n(R)`, then so is `H`; in particular, `K` finitely
   presented forces `H` finitely presented;
2. if `K` and `H` are finitely presented, then `δ_H ≼ δ_K`.

## Proof

1. **Labels along the orbit.** Local faithfulness at `κ` passes to every point `hκ`, because
   `h'` is trivial near `hκ` iff `h^{-1}h'h` is trivial near `κ`. For `y ∈ Hκ` and `k ∈ K`,
   let `δ(k, y) ∈ H` be the label of `k` at `y`, i.e. `h_i` for any piece `U_i ∋ y`.
   - This is well defined: two labels at `y` agree on the open set `U_i ∩ U_j ∋ y`, so they
     are equal by local faithfulness at `y`.
   - `k(y) = δ(k, y)(y) ∈ Hκ`.
   - The cocycle identity `δ(k k', y) = δ(k, k'y) δ(k', y)` holds, because `k k'` equals
     `δ(k, k'y) δ(k', y)` on a neighbourhood of `y`.
2. **The retraction.** Put `λ(k) = δ(k^{-1}, κ)^{-1}`, the label with which `k` arrives at
   `κ`. For `h ∈ H` we get `λ(h) = h`.
3. **Lipschitz.** Let `S` be a finite symmetric generating set of `K`, and let `C` be the
   largest `H`-length of a label occurring in the finitely many covers of the elements of
   `S`. Then:
   - `δ(s, y)` is one of those labels for every `y ∈ Hκ`;
   - by the cocycle identity, `λ(k s) = λ(k) · δ(s^{-1}, k^{-1}κ)^{-1}`;
   - so `d_H(λ(k), λ(ks)) <= C` in left-invariant word metrics, and `λ` is `C`-Lipschitz.
4. **The inclusion.** `ι : H -> K` is Lipschitz, since each of the finitely many generators
   of `H` is a word in `S`. Since `λ ∘ ι = id_H`, `H` is a quasi-retract of `K`. `∎`

**Variant (same proof).** Only points of the orbit `Hκ` were used. So it is enough that each
element of `K` has finitely many labels in `H` such that, near every point of `Hκ`, it agrees
with one of them. Elements may have breakpoints off `Hκ`, where they agree with no element
of `H`.

## Examples (hand remarks)

- **Transformation groupoids.** If `Γ` is finitely generated and acts on a Cantor set
  topologically freely, or merely locally faithfully at one point, then every finitely
  generated `K` with `Γ <= K <= [[Γ ⋉ X]]` has at most the finiteness of `Γ`. So a finitely
  presented topological full group of such an action needs a finitely presented `Γ`.
- **Thompson's `T` (by the variant).** `T` is the group of homeomorphisms of `RP^1` that are
  piecewise in `PSL_2(Z)`, with finitely many pieces and rational breakpoints, and it contains
  `PSL_2(Z)`. `T` is not inside `[[PSL_2(Z) | RP^1]]`, because of the breakpoints. But an
  irrational `κ` has an orbit of irrationals, which avoids all breakpoints, and `PSL_2(Z)` is
  locally faithful there. So `T` quasi-retracts onto `PSL_2(Z)`.
- **Where the hypothesis fails.** Weakly branch actions (for example Grigorchuk's group on
  the boundary of the binary tree) are locally faithful at no point, since rigid
  stabilizers of cylinders are nontrivial. In the finitely presented hosts of non-finitely
  presented groups that we know (Röver's `V_G` containing Grigorchuk's group, Nekrashevych
  groups, Belk--Hyde--Matucci germ extensions of `V`), the labels generate a group that
  contains `V`-type elements supported on small cylinders, so it is locally faithful at no
  point and the theorem says nothing.

## Lesson for general BH

A single locally faithful point turns "read the germ there" into a Lipschitz retraction. So
a host that is piecewise over a locally faithful acting group cannot be more finitely
presented than that acting group. Non-finite-presentability cannot be hidden in germs at an
infinite emitter, or anywhere else, as long as the labels act locally faithfully and lie in
the host. So a non-fp input can enter a finitely presented host in one of three ways:
- inside a finitely presented label group that contains it (a Clapham envelope, as in
  Track A);
- through labels that are locally faithful nowhere (branching with rigid stabilizers, or
  small-support `V`-type labels);
- through a label group that is not a subgroup of the host. For stabilizer engines this way
  is closed too: `F_B/D(F_B)` is finitely generated abelian, so `D(F_B)` fp gives `F_B` fp
  (`fp-stabilizer-engines-need-fp-vertex-groups`).

This is the carrier principle made exact on the finiteness side: the acting group must carry
the finite presentation itself.
