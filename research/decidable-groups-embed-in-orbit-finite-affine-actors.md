---
rg: 2
id: decidable-groups-embed-in-orbit-finite-affine-actors
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented S ⋊ W whose automorphism group W is finitely generated with finitely many orbits on S
distinct_from:
  permutational-boone-higman-conjecture: that asks for some finitely presented type (A) actor containing the input; this asks for an affine one, which is a special case by `orbit-finite-affine-actions-are-type-a`, so this implies that. The converse is not known.
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that is the inner case W = Inn(S) with S = T finitely presented and conjugacy-finite, which at G = Z would answer Makowsky's FP19; this allows outer automorphism groups acting with finitely many orbits, which does not presuppose FP19.
  decidable-inputs-have-fp-shell-envelopes: that asks for a finitely presented full Cantor envelope; this asks for an orbit-finite automorphism group of a countable group with finitely many element orders, and needs no Cantor space.
---

**OPEN.** For every finitely generated group `G` with solvable word problem there
are a countable group `S` and a finitely generated group `W <= Aut(S)` with:

1. `G` embeds in `Γ = S ⋊ W`,
2. `Γ` finitely presented,
3. finitely many `W`-orbits on `S`.

By `orbit-finite-affine-actions-are-type-a` the affine action of `Γ` on `S` is then
of type (A), so this implies `permutational-boone-higman-conjecture` (route
`pbh-via-orbit-finite-affine-actors`).

**Screens that come for free** (item 4 of the criterion):
- `W` must be finitely presented, since it is a retract of `Γ`.
- `S` realizes only finitely many element orders.
- If `S` is finite then `W` is finite, so only finite `G` fit; an infinite input
  needs an infinite `S` and an infinite `W`.

## Attempts

1. **Boolean factors over the Cantor set (calibration, not new inputs).**
   - Take `S = C(C, F_2)`, the locally constant functions on the Cantor set, and
     `W <= Homeo(C)` containing the standard binary `V`, acting by precomposition.
     `V` is transitive on proper nonempty clopen sets, so `W` has at most three orbits
     on `S` (`0`, `1`, and indicators of proper nonempty clopens). So the affine
     action is of type (A) as soon as `S ⋊ W` is finitely presented.
   - For `W = V`: with `σ` a fixed-point-free involution of the two-sheet cover
     `C × {0,1} ≅ C`, the centralizer `C_V(σ)` maps onto `V` with kernel the
     locally constant sheet swaps, giving `C_V(σ) ≅ C(C,F_2) ⋊ V`. This is a hand
     check: every `h ∈ V` lifts by acting on both sheets, and a sheet swap on a clopen
     set is a prefix replacement.
   - Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858v2 (abstract and introduction
     read from the PDF, pp. 1–2): the generalised groups `V_r(Σ)`, which include the
     Higman–Thompson groups, are of type `F_∞` under mild restrictions, "and this
     implies that also centralisers of finite subgroups are of type F_∞"; centralisers
     are extensions `K ↣ C(Q) ↠ V_(r_1) × … × V_(r_t)` with `K` locally finite. The
     theorem number and the exact restrictions were not pinned, so finite presentation
     of `C(C,F_2) ⋊ V` is recorded as expected, not established. If it holds, this
     is a finitely presented affine type (A) actor that is not of Mikhailova form.
   - **Why it gives no new inputs.** The inputs are subgroups of `W`. When `W` is a
     finitely presented subgroup of `Homeo(C)` containing `V`, its own action on
     clopen sets already has finitely many pair orbits (at most those of `V`), so it
     is a type (A) actor whenever clopen stabilizers are finitely generated. Whether
     finite presentation of `C(C,F_2) ⋊ W` forces those stabilizers to be finitely
     generated is not settled; either way the input side is the full Cantor route
     (`fp-full-binary-cantor-groups-have-type-a-actions`).
2. **Finitely supported factors: killed.** For `S = ⊕_X A` with a nontrivial finite
   group `A` and `W` permuting an infinite set `X`, the support size of an element is
   `W`-invariant and unbounded, so there are infinitely many orbits.
3. **Spreading the input over the factor: killed as a route.** If `G` is put into `S`
   (for instance `S = C(C, G)` with `W` containing `V` and pointwise conjugation),
   the finite set of `G`-conjugacy classes attained is invariant, so there are
   finitely many orbits only when `G` is conjugacy-finite. That is the FP19-type
   condition of `every-wp-group-embeds-in-fp-conjugacy-finite-group`. The input has
   to act faithfully as automorphisms, inside `W`.
4. **Element-order screen.** Item 4c of the criterion excludes every `S` with
   unboundedly many element orders, e.g. Hall's universal locally finite group, or
   any group containing elements of all finite orders.

## Next test

A finitely presented `W` that contains a decidable group with infinitely many
conjugacy classes and is not a subgroup of a full Cantor group, acting on a countable
group with finitely many element orders (an `F_p`-vector space of countable dimension
is the first candidate) with finitely many orbits, such that `S ⋊ W` is finitely
presented.
