---
rg: 2
id: support-constraints-on-v-subgroups-cannot-see-one-endedness
kind: claim
title: Free subgroups of PSL_2(Z) in Thompson's T satisfy every support and attractor constraint on main with full supports, so a surface-group obstruction in V must use one-endedness; finite attractor orbits force a normal subgroup trivial near the attractor
requires:
  - cyclic-centralizer-subgroups-of-v-touch-attractors
distinct_from:
  cyclic-centralizer-subgroups-of-v-touch-attractors: that is a necessary condition; this is its calibration, showing the condition (and the support-counting strategy built on it) holds for a torsion-free group with cyclic centralizers that does embed in V.
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that is the open survey Question 4.7; this shows which strategies cannot decide it.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

1. **Calibration.** Take `F ≤ PSL_2(Z) ≤ T ≤ V`, a free subgroup of rank 2. The inclusion
   `PSL_2(Z) ≤ T` is standard: Ghys–Sergiescu realize `T` as the piecewise-`PSL_2(Z)` homeomorphisms of the
   circle. This is recalled, not read at source here.
   - `F` is torsion-free with cyclic centralizers.
   - Each nontrivial element acts on the circle with at most two fixed points: two for a hyperbolic element,
     one for a parabolic one. In the Cantor model it therefore has finitely many fixed points, so its support
     is all of `C` and `W(g^k) = ∅`.
   - So `F` satisfies `cyclic-centralizer-subgroups-of-nv-have-meeting-supports` and
     `cyclic-centralizer-subgroups-of-v-touch-attractors` automatically. The same holds for every
     support-counting condition of the form "each support contains a point of `γ(A ∪ R)` for every `γ`",
     since every support is `C`.
   - **Consequence:** these ingredients cannot rule out a closed surface group in `V`. Any obstruction to
     survey Question 4.7 must use one-endedness, or another property that separates surface groups from `F_2`.
2. **Finite attractor orbits.** Let `Γ ≤ V` be a closed hyperbolic surface group, `g ∈ Γ` nontrivial, and `p`
   an attractor of a flow power `g^k`. Suppose the `Γ`-orbit of `p` is finite.
   - A finite-index `Γ' ≤ Γ` fixes `p`.
   - The germ map `Γ' → Germ_p(V) ≅ Z` is nonzero, because some power of `g` lies in `Γ'` and contracts at `p`.
     The germ group of `V` at the rational point `p` is cyclic.
   - Its kernel `K` consists of the elements of `Γ'` that are the identity near `p`.
   - `K ≠ 1`, since otherwise `Γ'` would embed in `Z`. `K` has infinite index, so it is a nontrivial normal
     free subgroup of infinite rank.
   - `K` fixes pointwise the closed `Γ'`-invariant set `C \ ⋃_{h ∈ K} supp(h)`, which contains `p`.
   - So a finite attractor orbit is not contradictory by itself. What it forces is a nontrivial normal subgroup
     that is locally trivial at a common fixed point.

**What would be needed.** A contradiction for one-ended `Γ` would need a statement tying locally trivial
normal subgroups, or infinite attractor orbits, to the Gromov boundary `S^1` of `Γ`. One example would be
that the orbit closure of `p` carries a `Γ`-equivariant map onto `∂Γ`. That map would be incompatible with the
Cantor topology of a finite union of cones. None of this is attempted here.
