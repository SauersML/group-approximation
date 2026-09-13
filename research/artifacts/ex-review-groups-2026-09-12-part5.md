# EX review, groups: part 5. Bernoulli absorption, the torsion-free wreath, dead-route sweep at `f79305e9c`

Lane `ex-verify-groups`, 2026-09-13, ~00:40 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 5.0 Sweep at tip `f79305e9c`

The two-stratum fixpoint was rebuilt (8,155 established claims; pass 1 = pass 2).

**New `requires: []` routes into famous targets.**
- `non-vtf-hyperbolic-via-lattice-forced-torsion-quotient` targets `non-virtually-torsion-free-hyperbolic-group`.
  It is killed by `lattice-forced-torsion-dies-in-hyperbolic-quotients`, which computes established through
  `kapovich-wise-rf-iff-finite-quotients`. The target computes open.
- `kt-canonical-hs-normalization-fails` is OPEN and carries `invalidates: [kt-pair-non-hyperlinear-commutant]`.
  That route requires the open `kt-centralizer-normalization-hs`, so it never fires either way. The edge is inert.

**Statuses of famous targets.** Every famous target of the reviewed lanes computes open, except
`infinite-simple-kazhdan-hyperlinear-group` (Pestov 9.1), which passed in part 1. Baseline-open roots that now
compute established: that one, plus three peer flips (two Boone–Higman roots, class-three unitary
components). Those belong to other reviewers.

## 5.1 ex-bernoulli-negative (44fec21fb7, d2a8ad5ce4, c52c701fd7). PASS

- **`bernoulli-factor-algebraic-actions-have-finite-stabilizers`.**
  - `f_a(x) = x(a)` is a nontrivial character, `H = Stab(a)`-invariant, with mean `0` and norm `1`.
  - Pulled back along a factor map it is an `H`-invariant unit vector in `L^2_0` of a Bernoulli shift.
  - Mixing, via finite-coordinate density and `h S ∩ S' = ∅` off the finite set `S' S^-1`, forces `H` finite.
  - Nonzero rows of `F_p[G]^n` have stabilizers of size at most `|supp|`.
- **`stable-finiteness-failure-is-algebraic-bernoulli-absorption`.**
  - *(1 ⇒ 2).* `BA = I` and `e = AB`. `ρ_B` is injective with image `R^n e`, so `R^n ≅ R^n ⊕ R^n(I-e)`.
  - *(2 ⇒ 1).* Dualize to `θ : R^n -> R^n ⊕ M`. `π = pr_1 θ = ρ_A` is onto with kernel `≅ M != 0`. A lift
    `ρ_B` of the basis rows gives `BA = I`, and `AB = I` would make `π` injective.
  - Continuous group isomorphisms preserve Haar measure, and `Hom(F_p[G]^n, F_p) = (F_p^n)^G` is the uniform
    shift.
  - (b) and (c) are algebra on top of Seward's equal-entropy theorem.
  - The `F_q` case goes through the regular representation `M_n(F_q[G]) -> M_(nd)(F_p[G])`.
  - Verdict PASS. Both conclusions it names are conditional, and the node says so: no group with `F_p[G]`
    not stably finite is known, and Bernoullicity of the absorbed factor is open.
- **`bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square`.**
  - *(2 ⇒ 1).* `X_h x X_h ≅ X_2h`.
  - *(1 ⇒ 2).* `d > 0` in `D(G)`, and from `X_a ≅ X_(a+d)` we get `X_b ≅ X_a x X_(b-a) ≅ X_(b+d)` for all
    `b >= a` (item 6). So `X_nd ≅ X_2nd = X_nd x X_nd` once `nd >= θ`.
  - Powers by induction.
- **`coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`.** Already reviewed, with two corrections, by
  `ex-verify-dynamics` (§1 of `ex-review-dynamics-2026-09-12.md`). Not duplicated here.

## 5.2 ex-left-orderable-nonsofic: `integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic` (f09f5eab75). PASS

- **Torsion-free.** `G` is torsion-free (the Belegradek–Osin cover node), so `Ĝ` is, and `L = ⊕ Z` is. A
  finite-order element maps to `1` in `Ĝ` and so lies in `L`, where it is trivial.
- **Finitely generated.** `Ĝ` is Kazhdan, and one lamp generates `L` as a module over the transitive action.
- **Rigid defect.** `e_o` centralizes `Γ̂`, and `[û e_o û^-1, γ] = e_(ûo) - e_(γûo) != 0` for
  `γ ∉ û Γ̂ û^-1`. By `sofic-groups-kill-rigid-compression-defects` (with `H = W_hat`, `G = Ĝ`, `Γ = Γ̂`),
  `W_hat` is nonsofic.
- **What is not claimed.** Unique products for `W_hat` (open), and left-orderability, which would need a
  left-orderable infinite Kazhdan group.

Credit: the node sets it against Fournier-Facio's imported torsion-free nonsofic group correctly. It is an
internal derivation, not a first example.

## Queue

- ex-determinant-monster: `rational-character-approximable-groups-obey-determinant`,
  `integer-root-limits-are-galois-balanced-serre-measures`, `unbalanced-eigenvalue-certifies-nonsofic-support`,
  `heavy-eigenvalue-gives-determinant-counterexample`, `serre-class-atoms-obey-degree-bound`.
- ex-lueck-approximation: the frame-complex L²-acyclicity chain.
- ex-weak-soficity: support and rank collapse, relator width.
- ex-fp-simple-sofic: amenable-orbit full groups.
- ex-atiyah-torsion-free: base change off a countable set.
