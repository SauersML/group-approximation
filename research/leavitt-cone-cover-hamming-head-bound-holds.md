---
rg: 2
id: leavitt-cone-cover-hamming-head-bound-holds
kind: claim
title: The cone-cover head bound holds for all permutation and finite-phase monomial representations, because the binary Leavitt unit group is nonsofic, so every refutation of the cone bound or of half rounding is a hyperlinear nonsofic group
distinct_from:
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that splits non-hyperlinearity of Delta into the unitary head bound (QC) and half rounding (HR) and proposes refuting (QC) with congruence-quotient representations; this proves (QC) outright for every permutation and every finite-phase monomial representation of the cover, and shows that any refutation of (QC) or (HR) produces a hyperlinear nonsofic group.
  leavitt-cone-cover-kernel-is-dense-in-every-compact-model: that kills exact compact-model invariants of the kernel K; this is an approximate (small-relator) statement in the Hamming metric, deduced from nonsoficity of the unit group.
  bounded-depth-symmetric-models-are-sofic-approximations: that is about the Jacobson group EL_n(J), whose soficity is open, and needs character asymptotics; this is about the Leavitt host Delta, whose nonsoficity is established, and needs only shadowing and tensor powers.
  openai-leavitt-unit-nonsofic: that is the nonsoficity theorem for the unit group; this transports it to a quantitative head bound on the residually finite cone cover, and to a calibration of the two sides of the (QC)/(HR) split.
artifacts:
  - research/leavitt-cone-cover-hamming-head-bound-proof.md
---

**ESTABLISHED** (route `leavitt-cone-cover-hamming-head-bound-proof`; lane swarm-0917-w17-w17-nh-last1,
calibration; unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`,
`leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`).
- `R = L_(F_2)(1,2)`, `Delta = St_20(R) = GL_20(R)`, simple; `z = x_13(s_1 t_1)`.
- `Gamma = Delta_+ *_(Delta_0) Delta_-`, the residually finite cone cover, with `p : Gamma -> Delta` onto and
  `K = ker p = <<k_1, ..., k_r>>`. The head `z` lies in the finite edge group `Delta_0`.
- For a permutation `u` of a finite set `X`, `d(u) = |{x : ux != x}| / |X|` (normalized Hamming distance to `1`).
- `C_m wr Sym(d) <= U(d)` is the group of monomial unitaries whose nonzero entries are `m`-th roots of unity
  (`m = 1`: permutation matrices). Norms on `U(d)` are normalized Hilbert--Schmidt.

**Statement.**
1. **(QC_H) Hamming head bound.** For every `ε > 0` there is `δ > 0` such that every action of `Gamma` on a
   nonempty finite set with `max_i d(k_i) <= δ` has `d(z) <= ε`.
2. **(QC_m) Finite-phase monomial head bound.** For every `m >= 1` and `ε > 0` there is `δ = δ(m, ε) > 0` such
   that every homomorphism `ρ : Gamma -> C_m wr Sym(d)` with `max_i ||ρ(k_i) - 1||_2 <= δ` has
   `||ρ(z) - 1||_2 <= ε`. So `(QC)` holds on the class of all such representations, for every `d`.
3. **Sofic head collapse.** Every asymptotic homomorphism `σ_n : Delta -> Sym(X_n)` in the Hamming metric
   has `d(σ_n(g)) -> 0` for every `g in Delta`; the same holds for asymptotic homomorphisms into
   `C_m wr Sym(d_n)` in normalized HS, for each fixed `m`.
4. **Calibration of the split.** If `(QC)` fails, or if `(HR)` fails, then `Delta` is hyperlinear, so the
   nonsofic unit group `R^x <= Delta` is hyperlinear, and `hyperlinear-nonsofic-group` (Pestov Question 3.4)
   and `binary-leavitt-unit-group-hyperlinear` are both resolved positively. Together with the established
   split, every outcome of the `(QC)/(HR)` pair resolves a flagship: `(QC) and (HR)` gives a non-hyperlinear
   group, and anything else gives a hyperlinear nonsofic group.

**Class killed.** Finite-phase monomial refutations of `(QC)`: next step 1 of the w16 Attempts entry of
`agent-leavitt-not-bcs-negative-root-corner`, carried out with permutation representations of congruence
quotients of the halves (regular, quasi-regular, Schreier-coset actions glued on `Delta_0`), or with
representations induced from characters of bounded order.
- *Invariant:* nonsoficity of `R^x` (`openai-leavitt-unit-nonsofic`), inherited by `Delta >= R^x`.
- *Death step:* the set-section shadowing turns the counterexample into a head-moving Hamming asymptotic
  homomorphism of `Delta`; simplicity and tensor powers make it a sofic approximation.
- *Also dead:* genuine representations pointwise HS-close to maps into `C_m wr Sym(d_n)` for one fixed `m`
  (route, last section).
- *Survivors:* genuinely non-monomial unitary representations of `Gamma`. Finding one that refutes `(QC)`
  resolves Pestov Question 3.4 (item 4).

**Scope.** This does not prove `(QC)` for unitary representations or `(HR)`, and it does not touch
`(LNC3)` beyond item 4. It shows that the refutation side of the w16 split is not a cheap computation.
