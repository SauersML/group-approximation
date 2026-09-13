---
rg: 2
id: relative-torsion-defect-mf-radical-step
kind: claim
title: A one-sided pair that exists only modulo an MF-invisible relative elementary subgroup still puts its defect ideal in the MF radical
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the absolute statement, for a one-sided pair of the ring itself; this is the relative form, where the pair and the torsion of its defect hold only modulo an ideal whose relative elementary subgroup is already MF-invisible.
  congruence-invisible-ideal-torsion-defect-step: that assumes the whole congruence kernel of the ideal is MF-invisible and is proved; this assumes only the relative elementary subgroup is, and is open because the gap between the two is a relative K_1 group.
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

**OPEN** (demoted 2026-09-13 after review by `un-verify-open`; the earlier proof route was withdrawn).

Let `R` be a countable unital ring, `J` a two-sided ideal, and `n >= 4`. Suppose

```text
EL_n(R,J) <= Rad_MF(EL_n(R)),     ts - 1 in J,     m(1 - st) in J for some m >= 1.
```

Is `EL_n(R, ReR + J) <= Rad_MF(EL_n(R))`, where `e = 1 - st`?

If the hypothesis is strengthened to the congruence kernel, `EL_n(R) n GL_n(R,J) <= Rad_MF(EL_n(R))`,
the conclusion holds: that is `congruence-invisible-ideal-torsion-defect-step`. Answering this claim
positively would make `mf-radical-contains-hilbert-hotel-elementary-subgroup` unconditional.

## Attempts

- **Run the printed proof in `Gbar = EL_n(R)/EL_n(R,J)` (withdrawn).** The ring facts the printed
  `prop:torsion-defect-ring` consumes (`ts=1`, `es=te=0`, `f_ij f_kl = delta_jk f_il`, `me=0`,
  `e != 0`) do survive reduction modulo `J`. But the group identities of that proof are matrix
  computations, not consequences of the Steinberg relations: the intertwining of Lemma l.866, `c` as a
  diagonal matrix, the commutator formula for `D(1 +- f_ij)`, `vcv^-1 = e_14(f_02)`, `vzv^-1 = z`,
  `[y,d] = z^-1`, `z^m = 1`. When the ring relations hold only modulo `J`, each identity holds in
  `Gbar` only up to an element of `(EL_n(R) n GL_n(R,J))/EL_n(R,J)`, the relative `K_1`-type slack,
  not exactly. Found by `un-verify-open` (review of 36226184dd).
- **Descend through the congruence kernel instead.** This works whenever the congruence kernel is
  MF-invisible (`congruence-invisible-ideal-torsion-defect-step`), but that hypothesis is genuinely
  stronger. **Calibration:** for the universal torsion-defect ring `A_m`, `m > 2`
  (`universal-torsion-defect-rings-have-exact-mf-radical`), `Rad_MF(EL_n(A_m)) = SL_fin(Z/m)` while
  the congruence kernel of `I_m` is `{g in GL_fin(Z/m) : det g = +-1}`, so the slack is a nontrivial
  central `C_2` lying outside the MF radical. The slack cannot be assumed away in general.
- **What a proof needs.** Either a lift of the pair to a genuine one-sided pair of `R` (the obstruction is
  an index in the slack group; see `hilbert-hotel-radical-is-reached-in-one-step`), or a version of the
  compression argument whose identities are Steinberg-group consequences valid in `Gbar` exactly.
- **Two repair routes (recorded by review, un-verify, 2026-09-13).** The exact gap: the identities of the printed
  construction hold exactly in `EL_n(R/J)`, and in `Gbar = EL_n(R)/EL_n(R,J)` only up to elements of
  `(EL_n(R) ∩ GL_n(R,J))/EL_n(R,J)`.
  - *Congruence-kernel invisibility as the induction hypothesis.* Assume `EL_n(R) ∩ GL_n(R,J) ≤ Rad_MF(EL_n(R))`.
    Radical descent through the exact reduction `EL_n(R) ↠ EL_n(R/J)` then gives the step with no quotient-group
    identity. This is landed as `congruence-invisible-ideal-torsion-defect-step`. Along the Hilbert-hotel chain it
    needs the congruence form at every successor stage, which is again a relative `K_1` question.
  - *Steinberg-group construction.* Put `U_m = Z⟨σ,τ⟩/(τσ − 1, m(1 − στ))`. Lifting entries along `U_m → R/J` gives
    a well-defined homomorphism `St_n(U_m) → Gbar`, since the Steinberg relations hold modulo `J` at generator level.
    The printed identities hold in `EL_n(U_m)`, so the construction runs in `Gbar` once they hold in `St_n(U_m)`, i.e.
    under control of `K_2(n, U_m) = ker(St_n(U_m) → EL_n(U_m))` on the words involved.

**Review (un-verify, 2026-09-13): GAP.** The transfer of the printed identities to `Ḡ = EL_n(R)/EL_n(R,J)` is justified only for single generators (`e_ij(x)` and `e_ij(x′)` with `x ≡ x′ mod J` differ by `e_ij(x′−x) ∈ EL_n(R,J)`). The identities the construction needs (`vcv⁻¹ = e_14(f_02)`, `vzv⁻¹ = z`, centrality of `z`, `[y,d] = z⁻¹`) are matrix identities proved by multiplication using `ts = 1`, `es = te = 0`, `me = 0`; with these holding only modulo `J`, the two sides differ by an element of `EL_n(R) ∩ GL_n(R,J)`, which need not lie in `EL_n(R,J)`. So the relations hold exactly in `EL_n(R/J)`, not in `Ḡ`, and the compression criterion needs exact relations in `B̄ ≤ Ḡ`. See `research/artifacts/un-review-2026-09-13-part8.md` §2.
