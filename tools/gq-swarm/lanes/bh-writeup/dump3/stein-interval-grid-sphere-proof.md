---
rg: 2
id: stein-interval-grid-sphere-proof
kind: route
title: Map the open interval to the poset of nonempty sets of atoms and apply Quillen's fiber lemma
target: stein-complex-elementary-intervals-are-grid-spheres
requires: []
---

Notation as in the target. Imports are from Belk--Zaremsky, arXiv:2001.04579 (TeX on MSI),
and from Quillen, *Homotopy properties of the poset of nontrivial p-subgroups of a group*,
Adv. Math. 28 (1978), Proposition 1.6 (the fiber lemma; the version BZ cite as
[quillen78]). The fiber lemma was not re-read at source by this lane.

**Step 1. The interval is a poset of partitions.** By BZ Proposition `prop:JoinForests` and
its proof, vertices of `F_q` above `[id_q]` correspond to unordered dyadic partitions of
`C^S(q)`, with `≤` corresponding to refinement, and any two have a least common refinement.
So `[v, w]` is the poset of dyadic partitions of `C^S(q)` that are refined by the partition
`π_f` of `f`. Write `Q = (v, w)`.

**Step 2. Atoms.** For a root `i` and a color `s`, let `z_i^s = [id ⊕ x_s ⊕ id]` (split cube
`i` in color `s`). Then `z_i^s ≤ w` iff `π_f` refines the `s`-halving of cube `i`, iff every
point of cube `i` has its coordinate `s` changed by `f_i`, iff `s ∈ SSpec(f_i)`. Let
`A = {(i, s) : s ∈ SSpec(f_i)}`.
- *Every `z ∈ Q` lies above an atom.* Represent `z = [e]` with `e` a nontrivial multicolored
  forest. Some tree `e_i` is nontrivial; let its root split be `x_s`. Then `z_i^s ≤ z ≤ w`,
  so `(i, s) ∈ A`.
- *Joins of atoms.* For `U ⊆ A` let `z_U` be the class of the forest splitting each cube `i`
  fully in the colors `U_i = {s : (i,s) ∈ U}`. It is the least common refinement of the
  `z_i^s` with `(i,s) ∈ U`, so `z ≥ z_U` iff `z ≥ z_i^s` for all `(i, s) ∈ U`. Also
  `z_U ≤ w`, since `π_f` refines each of these halvings.
- `A ≠ ∅`, since `f` is nontrivial.

**Step 3. The map to subsets.** Define `α(z) = {(i, s) ∈ A : z_i^s ≤ z}` for `z ∈ Q`. It is
order preserving, and nonempty by Step 2.

**Step 4. Grid case.** If `SSpec(f_i) = Spec(f_i)` for all `i`, then each nontrivial `f_i`
is an elementary tree whose pieces are cut in every color of `Spec(f_i)`. Its pieces are
elementary bricks, so they are exactly the `2^{|Spec(f_i)|}` full sub-bricks, and
`z_A = w`.
- Hence `α(z) ≠ A` for `z < w`, and `α` maps `Q` to the poset `B°` of proper nonempty subsets
  of `A`.
- For `U ∈ B°`, the fiber `α^{−1}(B°_{≥U}) = {z ∈ Q : z ≥ z_U}` has minimum `z_U`. Here
  `z_U ∈ Q`, because `U ≠ ∅` gives `z_U ≠ v`, and `U ≠ A` gives `z_U ≠ w`.
- So each fiber is a cone, hence contractible. By Quillen's fiber lemma,
  `|Q| ≃ |B°| ≅ ∂Δ^{|A|−1} ≅ S^{|A|−2}`, and `|A| = Σ_i |Spec(f_i)| = e(f)`.

**Step 5. Non-grid case.** Suppose some `i` has `SSpec(f_i) ⊊ Spec(f_i)`.
- The pieces of `π_f` in cube `i` use a color outside `SSpec(f_i)`, so `z_A < w`. Also
  `z_A ≠ v`, since `A ≠ ∅`.
- So `α` maps `Q` to the poset `B` of all nonempty subsets of `A`, and each fiber
  `{z ∈ Q : z ≥ z_U}` again has minimum `z_U ∈ Q`.
- By the fiber lemma `|Q| ≃ |B|`, which is a cone with apex `A`, hence contractible.

**Step 6. Relative homology.** `|[v, w]|` is a cone, hence contractible. As BZ note in the
proof of Proposition `prop:cible`, `|[v, w)| ∪ |(v, w]|` is the suspension of `|(v, w)|`,
with suspension points `v` and `w`. So
`H_k(|[v,w]|, |[v,w)| ∪ |(v,w]|) ≅ H̃_{k−1}(Σ|(v,w)|) ≅ H̃_{k−2}(|(v,w)|)`. Steps 4 and 5
give the stated values.

**Comparison with BZ.** BZ cover `|Q|` by the stars of the atoms and use the Nerve Lemma. The
nerve is the full simplex on `A` in the non-grid case and its boundary in the grid case;
this is the same dichotomy.
