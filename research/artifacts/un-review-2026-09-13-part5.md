# UN review, part 5: the MF spectrum of elementary groups

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-open-2`, landings `172dd02250` and `cebb682c41`,
artifact `research/artifacts/un-open-2-mf-spectrum-2026-09-13.md`.

| item | node | verdict |
|---|---|---|
| (1) | `mf-rigidity-is-monotone-in-matrix-rank` (+ `-proof`) | PASS (one sign wording note) |
| (2) | `mf-thresholds-rescale-under-matrix-amplification` (+ `-proof`) | PASS |

## 1. Monotonicity

- **Down-set.** The corner map `A ↦ diag(A, I_{M−N})` is an injective homomorphism `EL_N(R) → EL_M(R)` with
  `e_ij(r) ↦ e_ij(r)`. MF passes to subgroups (`non_mf_groups_exist.tex` l.1080).
- **Normal generation.** `w_ab = e_ab(1)e_ba(−1)e_ab(1)` is, in the `(a,b)` plane, `[[0,1],[−1,0]]` on columns:
  `(x_a,x_b) ↦ (x_b,−x_a)`. The node displays the row-vector action `(−x_b, x_a)`. Conjugation by `w_ab` sends
  `e_ij(r)` to `e_{i′j′}(±r)` with `a, b` interchanged; only the `±` matters. Transpositions generate `S_M`, and
  `r ↦ −r` is bijective, so the conjugates of `{e_12(r)}` contain every `e_ij(r)`. Since `N ≥ 2`, `e_12(r)` is in
  the corner copy, so its normal closure is `EL_M(R)`.
- **Up-set.** `φ∘i` is trivial, so `ker φ ⊇` the normal closure of `i(EL_N(R))`, which is `EL_M(R)`.
- **Exclusivity.** MF and MF-rigid together would make the identity trivial; but `e_12(1) ≠ I` because `1 ≠ 0`.
- **Corollary.** Not rigid gives a nontrivial homomorphism to an MF group, whose image is a nontrivial MF quotient.
  `mf(R) < rig(R)`.
- **Calibrations.** The Pestov ring has `(∞, ∞)`, since it is LEF in every rank. `L_k(1,2)` has `(1, 2)` by the
  rank-two theorem. Both consistent.

## 2. Rescaling

- **Lemma.** `EL_N(M_m(R)) = EL_{Nm}(R)` for `N ≥ 2`. It is the block identity already checked in part 3 §1: block
  elementary matrices are products of commuting elementary matrices, and an intra-block root is the commutator
  through another block.
- **`rig`.** `EL_N(M_m(R))` is rigid ⟺ `EL_{Nm}(R)` is rigid ⟺ `Nm ≥ rig(R)`, by the up-set on ranks `≥ 2`. So
  `rig(M_m(R)) = max(2, ⌈rig(R)/m⌉)`.
- **`mf`.** `EL_N(M_m(R))` is MF ⟺ `Nm ≤ mf(R)`, so `mf(M_m(R)) = ⌊mf(R)/m⌋` when that is at least 2, and `1`
  otherwise. Checked, including the degenerate `mf(R) = 1`.
- **Corollary.** Finiteness of `rig` and infiniteness of `mf` are stable. Checked.
- **State-space remark.** For simple `R`, a nonzero idempotent `e` over `M_j(R)` satisfies `[1] ≤ m[e]` and
  `[e] ≤ j[1]`. So a state with `ν(e) > 0` has `ν([1]) ≥ ν(e)/j > 0`, and "`V(R)` has no nonzero state" implies
  that `[R]` is paradoxical (part 2), hence `rig(R) < ∞` (part 3 §1). Checked; the converse is correctly left open.

## 3. Subsumption and display

- **Scan:** claims on full MF radical / MF rank thresholds / matrix amplification. `binary-leavitt-all-ranks-full-mf-radical`
  and the rank-two theorem are special cases.
- **Nothing states the monotone structure:** no established node covers it, and none contradicts it.
- **Displays recomputed:** `w_ab`, `rig(M_m(R))`, `mf(M_m(R))`, `[1] ≤ m[e]`, `[e] ≤ j[1]`. Only the sign
  convention note applies.
