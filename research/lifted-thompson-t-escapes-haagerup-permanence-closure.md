---
rg: 2
id: lifted-thompson-t-escapes-haagerup-permanence-closure
kind: claim
title: "T-bar embeds in no group built from amenable, cubically proper or amenable-by-residually-finite groups by subgroups, finite products, finite-index overgroups, directed unions, extensions with amenable quotient, restricted permutational wreath products and graphs of groups with finite edge groups; so no permanence argument proves lifted-thompson-t-is-a-t-menable, or nV Haagerup through T-bar"
distinct_from:
  lifted-thompson-t-perfect-centre-cubically-elliptic: that proves perfectness, no finite quotients and cubical ellipticity of z; this uses those as inputs, adds the normal-subgroup lemma (every normal subgroup is central or everything), and closes the class of hosts under seven group operations
  thompson-f-in-permanence-closure-only-via-base-copy: that is the analogous closure theorem for Thompson's F, whose invariant is "contains a copy of F" and whose tree lemma is relative; here the invariant is "contains T-bar", and the inputs are the central divisible element z and the absence of finite quotients
  lifted-thompson-t-is-a-t-menable: that is the open target; this only kills the permanence-closure route to it, and names the two operations through which T-bar can still escape (central extensions and unrestricted products)
  divisible-elements-act-elliptically-on-trees: that makes elements with many roots elliptic on trees; this uses it once, in the finite-edge graph-of-groups step, to put all of T-bar in a vertex group
  hall-quotient-avoids-v-circle-groups-and-periodic-ends: that uses Higman's theorem for Hall's group; here it is used only in a remark, to show T-bar is not a subgroup of V
  abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q: that kills abelian-lamp wreath hosts for U3(Q) and Aff(Q); this kills restricted wreath hosts with arbitrary lamps for T-bar
  haagerup-splits-as-coset-plus-subgroup-properness: that splits Haagerup for nV into coset properness and properness on the subgroup; this shows the subgroup half for T-bar cannot be imported from any known Haagerup group by permanence
---

**ESTABLISHED** by `lifted-thompson-t-escapes-haagerup-permanence-closure-proof`. The proof is
elementary once its inputs are granted. Not independently reviewed, and no priority is claimed.

## Setting

- `T̄` is the lift of Thompson's `T` to `R`, and `z(x) = x + 1` generates its centre `⟨z⟩`.
  This is as in `lifted-thompson-t-perfect-centre-cubically-elliptic`.
- `T̄` is finitely generated: take lifts of a finite generating set of `T` together with `z`.
- `T̄ ⊆ C(C,Z) ⋊ T ⊆ C(C,Z) ⋊ V ⊆ 2V`. For `n ≥ 2`, `2V ⊆ nV`.
  So Haagerup for any of these groups implies Haagerup for `T̄`.

**Definition.** Let `𝒦` be the smallest class of groups with the following two properties.

It contains three kinds of building blocks:
- **(B1)** every amenable group;
- **(B2)** every group with a commensurating action (an action on a set `X` with a commensurated
  subset `A`) whose wall count `g ↦ |gA Δ A|` is proper. This includes every group acting
  properly on a CAT(0) cube complex. Examples: `F`, `T`, `V` (Farley), Hughes' LFD groups, and
  the zipper and cubical constructions recorded on `brin-thompson-groups-nv-are-a-t-menable`;
- **(B3)** every group `G` with a homomorphism `φ : G → R` whose kernel is amenable, where `R`
  is residually finite or is a subgroup of `GL_n(k)` for some field `k`. Examples: all residually
  finite groups, all linear groups (not necessarily finitely generated), and all subgroups of
  connected Lie groups. For the last, take `φ = Ad`, whose kernel is central.

It is closed under seven operations:
- **(P1)** subgroups;
- **(P2)** finite direct products;
- **(P3)** restricted permutational wreath products `Γ ≀_X G = (⊕_X Γ) ⋊ G`, for any action of
  `G` on any set `X`;
- **(P4)** fundamental groups of graphs of groups with finite edge groups. This includes free
  products, amalgams over finite groups and HNN extensions over finite groups;
- **(P5)** extensions `1 → N → G → Q → 1` with `N ∈ 𝒦` and `Q` amenable;
- **(P6)** directed unions;
- **(P7)** overgroups of finite index.

`𝒦` contains the standard Haagerup permanence closure of the Haagerup groups among these
blocks, and more. For example (B3) contains residually finite groups with property (T). The class is chosen to
be large on purpose, so that excluding `T̄` from it is a strong statement.

## Statement

1. **Normal subgroups.** Every normal subgroup of `T̄` is `⟨z^j⟩` for some `j ≥ 0`, or `T̄`.
2. **Nonamenability.** `T` has no invariant probability measure on `S^1`, so `T` and `T̄` are
   nonamenable.
3. **Escape trichotomy.** Suppose `T̄ ≤ G` and `1 → N → G → Q → 1` is exact. Then exactly one of
   the following holds:
   - `T̄ ≤ N`;
   - `T̄ ↪ Q`;
   - `T̄ ∩ N = ⟨z^m⟩` for some `m ≥ 1`, and `T̄/⟨z^m⟩ ↪ Q`.

   If `Q` is amenable, only `T̄ ≤ N` is possible.
4. **Wreath products.** If `T̄ ≤ Γ ≀_X G`, then `T̄ ↪ Γ` or `T̄ ↪ G`. If `Γ` is abelian, then
   `T̄ ↪ G`.
5. **Finite-edge graphs of groups.** If `T̄ ≤ π_1(𝔾)` for a graph of groups `𝔾` with finite edge
   groups, then `T̄` lies in a conjugate of a vertex group.
6. **Main theorem.** `T̄` embeds in no group of `𝒦`.

   Consequently, no group containing `T̄` lies in `𝒦`. This covers `C(C,Z) ⋊ T`,
   `C(C,Z) ⋊ V`, `2V` and `nV` for `n ≥ 2`.

## What it kills

**The class.** Every attempt to prove `lifted-thompson-t-is-a-t-menable`, or to prove `nV`
Haagerup through its subgroup `T̄`, that works by exhibiting `T̄` (or an overgroup) inside
a group assembled by standard Haagerup permanence from known Haagerup groups. Named members:
- Brothier-type wreath hosts `K ≀_{Q_2} V` and their iterates;
- amalgams and HNN extensions of cubical groups over finite subgroups;
- "amenable-by-cubical" and "cubical-by-amenable" towers;
- linear or Lie hosts, and residually finite hosts with amenable kernels;
- directed unions of any of these.

**The invariant.** Three facts about `T̄`:
- every normal subgroup is central or all of `T̄` (item 1);
- `T̄` has no proper finite-index subgroup;
- the central element `z` has roots of every order and is elliptic in every commensurating
  action.

**Where every member dies.** Look at the first operation (P2)–(P7) in the construction of the
host. The corresponding item 3, 4 or 5, or the finite-generation or finite-index step, pulls
`T̄` back into one of the inputs. After finitely many steps `T̄` must sit inside a building
block. There it dies:
- in (B1), by nonamenability (item 2);
- in (B2), because `z` has bounded wall count (input `lifted-thompson-t-perfect-centre-cubically-elliptic`,
  item 4) but infinite order;
- in (B3), because every image of `T̄` in a residually finite or linear group is trivial, so `T̄`
  would lie in the amenable kernel. For linear targets this uses Malcev
  (`finitely-generated-linear-groups-are-residually-finite`).

## Sharpness: the two escapes

The closure operations that are *missing* from (P1)–(P7) are exactly the ones through which
`T̄` escapes.
- **Central extensions.** `T̄` is a central extension of `T ∈ (B2)` by `Z`. Item 3 shows this is
  the only extension shape that can carry `T̄` past a quotient that does not contain it. The
  central-extension permanence question for `T̄` is the one the GJV survey calls widely open.
- **Unrestricted products.** By `lifted-thompson-t-quotients-are-rotation-centralizers`, the maps
  `ι_k : T̄ → C_T(r_k) ≤ T` have kernels `⟨z^{2^k}⟩`, whose intersection is trivial. So
  `T̄ ↪ ∏_{k ≥ 0} T`, and `T̄` is residually `T`. The finite-product step (P2) cannot be extended
  to countable unrestricted products.
- **Consequence for the goal.** Any proof of `lifted-thompson-t-is-a-t-menable` must build a new
  cnd function that is proper on `⟨z⟩`. It cannot be pulled back from a group in `𝒦`. This is a
  heuristic pointer, not a theorem: the two natural places to look are the central extension
  itself (the Euler-class direction) and residual limits of `T`-representations (the twist-gap
  direction of `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`). It cannot come from a
  permanence theorem.

## Remark: T-bar is not a subgroup of V

`T̄` contains the translations `x ↦ x + d` for `d ∈ Z[1/2]`, which form a copy of `Z[1/2]`.
Higman's theorem (verbatim in `hall-quotient-avoids-v-circle-groups-and-periodic-ends`, from
BBMZ arXiv:2306.16356v3) says no non-cyclic subgroup of `Q` embeds in `V`. So `T̄` embeds in
neither `V`, `T` nor `F`. This is independent of item 6, and it corrects "not a subgroup of `V`
in any known way" on `lifted-thompson-t-is-a-t-menable` to "not a subgroup of `V`".

## Not claimed

- Graph products with infinite edge groups, amalgams over infinite subgroups, and measure
  equivalence or other non-embedding permanence are not covered.
- Nothing here decides whether `T̄` is Haagerup. The theorem is a route kill, not a refutation.
- Whether `T̄` lies in the closure of `𝒦` under central extensions by `Z` is open. `T̄` itself
  shows that this closure is strictly larger than `𝒦`.
