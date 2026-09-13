# UN review, part 2 (lane un-verify-3, 2026-09-13)

Scope:
- the re-check of un-tarski's repair (0156bb3f0a);
- the priority nonsoficity landing of un-hyperlinear-paradox (82478cbb12), including its Lean backing;
- the stability and projective-nonsoficity nodes of un-stability-nonsofic (13fd21b643, 3c64a92ef3), queued by main.

Method as in part 1: re-derivation, quote and declaration checks, model tests, an untruncated title scan, and display
checks.

**Summary.** 7 PASS, 0 GAP, 0 FAIL. One display slip is recorded in §6. The only new content in the nonsofic boundary
claim is the explicit Leavitt family, since the quotient statement is a special case of an established node.

| § | Node | Verdict |
|---|---|---|
| 1 | `unperforated-paradox-makes-steinberg-purely-infinite` (repaired) and `invariant-measure-gives-rank-function-in-char-zero` | PASS |
| 2 | `boundary-crossed-product-carries-leavitt-family` | PASS |
| 3 | `infinite-simple-group-permutation-stable-iff-nonsofic` | PASS (likely folklore) |
| 4 | `halvable-corner-makes-projective-elementary-groups-nonsofic` | PASS |
| 5 | `purely-infinite-simple-projective-el-groups-stable-nonsofic` | PASS |
| 6 | `boundary-action-simple-kazhdan-group-is-nonsofic` | PASS (display slip; subsumed, see below) |

## §1 Re-check of the un-tarski repair: PASS

- **Statement.**
  - Exhaustive over every field: no invariant measure gives branch 2.
  - Exclusive for `k ⊆ ℂ`: a measure gives a faithful rank function, hence stable finiteness, contradicting branch 2.
  - No exclusivity is claimed in characteristic `p`. The node says why: exclusion needs *measure ⟹ stably finite*,
    which is Kaplansky-hard, and `ι` is not known to reflect paradox.
- **Route.** It requires `full-defect-ring-non-mf-at-rank-two` (established), which supplies rank two. From
  `2[1] ≤ [1]` there are `s_1, s_2, t_1, t_2` with `t_i s_j = δ_ij`, and `t_2(1 − s_1t_1)s_2 = t_2s_2 − t_2s_1t_1s_2 = 1`,
  so `1 − s_1t_1` is a full defect with `t_1 s_1 = 1`. It also requires the char-zero node for the exclusivity clause.
- **Char-zero node.** The new `distinct_from` entry names `char-zero-steinberg-stably-finite-iff-invariant-measure`.

## §2 boundary-crossed-product-carries-leavitt-family: PASS

- **Set identities.** For letters `c, c'` of `F_d`:
  - (I1) `c·C(c^(-1)) = ∂F_d \ C(c)`, since words beginning `c^(-1)` lose that letter;
  - (I2) `c·C(c') = C(cc') ⊆ C(c)` for `c' ≠ c^(-1)`;
  - (I3) the `2d` first-letter cylinders partition `∂F_d`.
- **Relation used.** `P_U u_g = u_g P_(g^(-1)U)`.
- **Products.**
  - `t_i s_i`: the four terms are `P^+`, then `u_(c^(-1))P_(C(cc))(1−P^+) = 0`, then `0`, then
    `P_(∂\C(c))(1−P^+) = 1 − P^+`. Sum `1`.
  - `s_i t_i = P^+ + P^-`, using (I1) for `c` and `c^(-1)`.
  - `t_i s_j = 0` for `i ≠ j`: all four terms vanish by disjointness and by `C(ec^(±1)) ⊆ C(e)` against `1 − P_(C(e))`.
  - `Σ_i s_i t_i = 1` by (I3).
- **Scope.** Any unital coefficient ring works.
- **Model tests.** `d = 1` gives a unit, correctly: ℤ has invariant measures on its ends. The Pestov ring admits no
  such family, since `rk(1) = d·rk(1)`.

## §3 infinite-simple-group-permutation-stable-iff-nonsofic: PASS, likely folklore

- **Easy implications.** (2)⇒(3)⇒(4) are immediate. (4)⇒(2): every homomorphism of an infinite simple group to a
  finite symmetric group is trivial. (2)⇒(1): a sofic approximation is an almost homomorphism with `d → 1`.
- **(1)⇒(2), the limit kernel.** Put `N = {g : lim_ω d(φ_n(g),1) = 0}`.
  - Subgroup: `d(φ(gh),1) ≤ defect + d(φ(g),1) + d(φ(h),1)`, and
    `d(φ(g^(-1)),1) = d(φ(g)φ(g^(-1)), φ(g)) ≤ d(φ(g)φ(g^(-1)),1) + d(φ(g),1)`.
  - Normal: `d(φ(h^(-1)), φ(h)^(-1)) = d(φ(h)φ(h^(-1)),1) → 0`, so conjugation costs `o(1)`.
  - Simplicity then gives `N = 1`.
- **(1)⇒(2), amplification.** `φ^(m)` on `[k_n]^m` has fixed-point fraction `(1 − d)^m`, and the defect grows at most
  `m`-fold. Choose `m` and then `n` from an `ω`-large set. Separation on pairs comes from enlarging `F` by `FF^(-1)`.
- **Model tests.** `A_5` is excluded by infiniteness; `ℤ` by simplicity.
- **Scope.** Stability is defined through almost homomorphisms, stated in the node. The equivalence with the
  Arzhantseva–Păunescu relator form is only recalled, and nothing depends on it.
- **Novelty.** A standard limit-kernel plus amplification argument, very likely folklore; no source located.

## §4 halvable-corner-makes-projective-elementary-groups-nonsofic: PASS

- **The proper halvable idempotent `e' = s_0 t_0`.**
  - Idempotent: `s_0 t_0 s_0 t_0 = s_0 e t_0 = s_0 t_0`.
  - Nonzero: `t_0 e' s_0 = e`.
  - Proper: `e' s_1 = 0` while `t_1 s_1 = e ≠ 0` forces `s_1 ≠ 0`.
  - `e'A ≅ eA` through `x ↦ s_0x` and `y ↦ t_0y`, hence halvable.
- **The corner copy.** `κ_n(g) = g + (1−e')1_n` is multiplicative and unital, and injective because
  `g = e'1_n κ_n(g) e'1_n`. It sends `1 + bE_ij` to itself, and `EL_n(A) ≤ EL_(nd)(R)` by block factorization.
- **Scalars.** If `κ_n(g) = λ1`, right multiplication by `(1−e')1_n` gives `(λ−1)(1−e') = 0`, so `λ = 1`.
- **Requires.** `d-ary-leavitt-groups-nonsofic-over-finite-fields` (Lean-backed, §6) and `sofic-passes-to-subgroups`
  (established, kernel-checked).
- **Model tests.** `M_2(F_q)` has no halvable idempotent; for `L_(F_3)(1,2)` the scalar `−1` is handled by step 4.

## §5 purely-infinite-simple-projective-el-groups-stable-nonsofic: PASS

- **Nonsoficity.** `agp-purely-infinite-simple-rings-have-cancellative-projectives` (established import) makes `V(R)*`
  a group, and its neutral element is halvable. §4 with `d = 1` and `C = Z ⊆ k^x·1` gives nonsoficity.
- **Infiniteness.** `{1 + rE_12}` is infinite and meets the scalars trivially.
- **Stability.** For simple `S_N`, §3 gives stability with trivial correcting homomorphisms, and `S_N` is not
  residually finite.
- **Wording note.** "Permutation stable" is inherited in §3's almost-homomorphism sense.

## §6 boundary-action-simple-kazhdan-group-is-nonsofic: PASS

- **Nonsofic groups.** `R_∂` is a countable nontrivial algebra over finite `k` with a unital `d`-ary family (§2), so
  `EL_N(R_∂)` is nonsofic for `N ≥ 2`.
- **Corner copy.** `θ(x) = s_1 x t_1` is a unital isomorphism onto `eR_∂e` with inverse `y ↦ t_1 y s_1`. With
  `Φ(X) = X + (1−e)I_N`, the composite `ψ = Φ∘EL_N(θ)` is injective, and `ψ(X) = λI` forces `λ = 1`. Hence every
  `EL_N(R_∂)/C` is nonsofic.
- **Simple quotient.** For `N ≥ 3`, `Z ⊆ k^x I` by the reviewed `steinberg-elementary-groups-are-simple-mod-centre`,
  since the boundary groupoid is minimal and effective.
- **Lean backing.**
  - The d-ary declaration is `GroupApproximation.CompleteMatrixFamily.elementary_not_isSofic (m) (hm : 0 < m) :
    ¬ IsSofic (elementaryGroup (Fin (m + 1)) A)`, in `GroupApproximation/Leavitt/AryEndpoints.lean`.
  - Its variables: `k` a finite field; `A : Type`, a ring with `[Algebra k A] [Countable A] [Nontrivial A]`;
    `F : CompleteMatrixFamily A (Fin (n+2))`, whose fields are `right i * left j = δ_ij` and `Σ left i * right i = 1`.
    These are exactly the boundary family's relations.
  - `IsSofic` (`Sofic/Sofic.lean:183`) is the standard local Hamming definition, with multiplicativity on `F × F`
    and separation `≥ 1 − ε`.
  - The module is root-imported (`GroupApproximation.lean:702`); `AryEndpoints.lean` and `FamilyRankFour.lean` contain
    no `sorry`, `admit` or `axiom` tokens.
  - `#print axioms`, run on MSI with `lake env lean` in the warm bc clone (olean of 2026-09-11; the source's last
    commit is the 09-12 restore, with content unchanged):
    - `CompleteMatrixFamily.elementary_not_isSofic` depends on `[propext, Classical.choice, Quot.sound]`;
    - `FamilyRankFour.elementary_not_isSofic` depends on `[propext, Classical.choice, Quot.sound]`.
  - `metadata/AUDIT_SURFACE.md` lists the binary `FamilyRankFour.elementary_not_isSofic`.
- **Display slip.** The route cites "Lean `LeavittFamily.elementary_not_isSofic`" for the d-ary input; the declaration
  used is `CompleteMatrixFamily.elementary_not_isSofic`.
- **Subsumption (untruncated title scan for nonsofic, simple and Kazhdan).**
  - `halvable-corner-makes-projective-elementary-groups-nonsofic` (§4) implies the quotient statement, because `R_∂`
    has a halvable idempotent.
  - `purely-infinite-simple-projective-el-groups-stable-nonsofic` implies it once `R_∂` is known to be purely infinite
    simple.
  - Simple Kazhdan nonsofic groups are already on main (Leavitt units: `openai-leavitt-unit-nonsofic`,
    `leavitt-unit-group-is-simple-fa-nonsofic`).
  - So the new content of this landing is the explicit boundary family (§2) and its role as the paradox mirror of
    Pestov's group. The node's `distinct_from` should also name `halvable-corner-makes-projective-elementary-groups-nonsofic`.
- **Consistency.** `boundary-simple-kazhdan-hyperlinear-nonsofic-separation` has no route and stays open.
