---
rg: 2
id: torsion-defect-costs-nothing-in-bhm-germ-complexes
kind: claim
title: Nonzero germ defect is not a finiteness obstruction when the defects are torsion; a bounded full contracting RSG with finite defect group is F_infinity, because defect only splits the portraits of the BHM germ complex into finitely many orbits; defects at fixed singular points are always torsion, and a half-shift over the 3-shift gives an F_infinity example with defect 1 in Z/2
requires:
  - bounded-defect-free-full-contracting-rsgs-are-f-infinity
distinct_from:
  bounded-defect-free-full-contracting-rsgs-are-f-infinity: that needs zero defect for BHM's localization axiom; this drops the axiom, shows BHM's complex still works when defects are torsion, and so generalizes that theorem.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; not reviewed; credit to Belk–Hyde–Matucci, whose
complex is used unchanged).
- Inputs: those of the parent node, i.e. BHM's germ complex, Matui's bisections, and the twisted-BT stabilizer
  reduction.
- Section 3 is analysis. No computation was run.

## Setting

- The setting and notation are those of `bounded-defect-free-full-contracting-rsgs-are-f-infinity`.
- `Δ` is the set of defects `d_g(p)` of singular germs, and `⟨Δ⟩` is the **defect group**.
- A B-germ `(Bh)_p` has the well-defined defect `d_h(p)`, since `d_{bh}(p) = d_b(hp) + d_h(p)` and B-germs are
  canonical.
- The **total defect** of a portrait `γ` is `Σ_p d(γ(p))`.

## Theorem

Let `L` be a bounded full contracting RSG with `⟨Δ⟩` finite. Then:
- `L` is `F_∞`;
- so are its finite-set stabilizers;
- `SV_L` is an `F_∞` simple group.

## Proof: BHM's argument with the localization axiom removed

1. **Zero-sum portraits are portraits of elements.** Let `γ` have germs `(Bg_i)_{p_i}` with total defect 0.
   - Replace `g_i` by `b_i g_i` (`b_i ∈ B`) so that the points `g_i(p_i)` are distinct.
   - Take disjoint small cones `U_i ∋ p_i`, avoiding the other singular points of `g_i`, with the sets `g_i(U_i)`
     pairwise disjoint.
   - Then `[E ∖ ⋃U_i] = [E ∖ ⋃ g_i(U_i)]`, because the total defect is 0. So a compact open bisection `k` of
     `G_Σ|_E` maps one onto the other (Matui, as in the parent node).
   - `h = g_i` on `U_i` and `h = k` elsewhere lies in `L`, and its portrait is `γ`.
   - Conversely, every element's portrait has total defect 0 (parent node, Proposition 2.2).
2. **Total defect is an orbit invariant, and there are finitely many orbits.**
   - `g·γ` has total defect `total(γ) + Σ_{sing(g^{-1})} d_{g^{-1}} = total(γ)`.
   - Fix `c ∈ ⟨Δ⟩` and a finite standard set of germs `Q_c` with total `−c`. For `γ` with total `c`, `γ ⊔ Q_c`
     (at fresh points) is zero-sum, so it is `portrait(h)`, and then `h·γ` is supported on `h(Q)` with the germ
     types of `Q_c`.
   - Using `B` to move points within their B-orbits (finitely many tail classes) leaves finitely many orbits of
     portraits for each `c`.
   - Since `⟨Δ⟩` is finite, the vertices of `K_{≤n}` fall into finitely many `L`-orbits.
   - The same count, with `M ⊆ M'` hidden sets, handles cubes.
3. **Stabilizers.** The stabilizer of a portrait supported on `P` consists of the `g` with:
   - `g(P) = P`;
   - `sing(g) ⊆ P`;
   - finitely many germ equations at `P`.

   It contains `Fix_B(P ∪ M')` with finite index, because the germ quotients `(L)_p/(B)_p` are finite (BBMZ
   `prop:CyclicStabilizers`). That group is `F_∞` (parent node, item (2)). Cube stabilizers are the same.
4. **Links.** BHM's `K = ∏'_p T_p` and its Morse function do not involve the group. Descending links are joins of
   the discrete sets `Bgerm(L,p)` (BHM `prop:nConnected`), so `K_{≤n}` is `(n−1)`-connected.
5. **Brown's criterion** on `K_{≤n}` gives `F_n` for every `n`. The finite-set stabilizers and `SV_L` follow as
   in the parent node. The members of `𝓕(L)` have their defects in `⟨Δ⟩`. ∎

**So localization was used only to get transitivity on portraits.** The finite count of orbits is what Brown's
criterion needs.

## When the defect group is finite

- **Fixed points.** If `g(p) = p`, then `d_g(p)` is torsion.
  - `(B)_p` has finite index `m` in `(L)_p`, so `g^m`'s germ is canonical.
  - The cocycle rule at a fixed point gives `m·d_g(p) = d_{g^m}(p) = 0`.
- **One tail class.** If all singular points lie in one B-orbit, then every singular germ is a B-translate of a
  germ fixing a base point. So `Δ` is torsion, and `⟨Δ⟩` is finite (a finitely generated torsion abelian group).
- **Finite homology.** If `coker(I − A^T)` is finite, i.e. `det(I − A) ≠ 0`, then `⟨Δ⟩` is finite. This covers
  the full `d`-shifts: `Z/(d−1)`.
- **Open case.** A non-torsion `⟨Δ⟩` would require transfer germs between different tail classes whose defect has
  infinite order. Then `K_{≤0}` has infinitely many orbits. Whether that is a genuine obstruction, or only a
  failure of this complex, is **open**.

## Example: nonzero defect, and F_∞

- **The space.** The 3-shift `{0,1,2}^ℕ`, with `B = V_3` and `H_0 = Z/2` (every cone has class 1).
- **The element τ.** List the branches along the ray `1^∞` as `C_0, C_2, C_{10}, C_{12}, C_{110}, …`. Then `τ`
  maps each branch onto the next one by the canonical similarity, and fixes `1^∞`.
  - `τ² = σ` near `1^∞`, where `σ` is the canonical shift `1^k w ↦ 1^{k+1}w`.
  - `τ` is singular only at `1^∞`.
- **Self-similar form.** `τ`'s local action at every `1^k` is `t` with `t(0x) = 2x`, `t(2x) = 10x`,
  `t(1y) = 1t(y)`.
- **Defect.** `t` maps `C_∅` onto `C_1 ⊔ C_2`, of class 0, while `[C_∅] = 1`. So `d_τ(1^∞) = 1 ≠ 0`.
- **The group.** Let `L` be the full closure of `⟨V_3, τ⟩`.
  - Its nucleus is finite: `id`, `t`, and the local action of `τ^{-1}`, since all odd powers of `τ` have deep local
    action `t` or its inverse type (lane check).
  - Every element is singular only on the `V_3`-orbit of `1^∞` (bounded, one tail class).
  - So the Theorem applies: **`L` is `F_∞`** although no element is singular at exactly one point. Every element
    has an even number of singular points.

## 3. BBMZ hosts (analysis)

- **Free groups on a basis.** The nucleus is trivial, so `L = V_Σ`, which is `F_∞` (Matui). Nothing new.
- **Surface groups.** The BBMZ host is `F_∞` if two conditions hold:
  - (i) boundedness: no two distinct cycles in the non-identity part of the nucleus automaton are joined by a path;
  - (ii) `⟨Δ⟩` finite, for instance `det(I − A) ≠ 0` for the atom type graph of `Γ ∗ Z`.

  Both are finite computations from the type graph and the nucleus. Neither has been run. The pentagon evidence
  (4 persistent chains per generator) fits (i). These groups already have `F_∞` hosts through 2V, so this would
  test Question 1.2 and would not extend Zaremsky's answer.
- **Boundary dimension ≥ 2 (all Kazhdan cases).** Singular sets are expected to be uncountable (exponential
  activity), so this Theorem does not apply.

## Lesson for general BH

- **Obstructions and failures of method can be separated by counting orbits.**
  - An invariant that splits the portraits of a germ complex into finitely many orbits is only bookkeeping.
  - Torsion defect is of this kind: it destroys BHM's localization but not its finiteness proof.
- **What is left.** Only a non-torsion invariant, or uncountable singular sets, could be a genuine obstruction.
  - For Question 1.2 on hyperbolic hosts, the defect question is settled up to the torsion condition.
  - The real frontier is activity, which is driven by boundary dimension.
