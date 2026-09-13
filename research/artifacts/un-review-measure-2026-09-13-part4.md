---
rg: 2
title: "UN review, rung (L⇒): LEF elementary groups force LEF rings, simple LEF rings are exactly matricial (2026-09-13)"
kind: artifact
---

Lane `un-verify-measure`, 2026-09-13. Part 4 (parts 1–3: `un-review-measure-2026-09-13-part1.md` … `part3.md`).
Reviewed: `un-lef-converse` landing de117129bd, artifact `research/artifacts/un-lef-converse-2026-09-13-part1.md`.
No FAIL.

## F1 `lef-elementary-groups-force-lef-rings`: PASS

- **Step 1 (cover).**
  - A = Z⟨x_r : r ∈ W⟩ is finitely presented: it is free on finitely many generators.
  - S = {x_ij(1)^{±1}, x_ij(x_r)^{±1}} generates St_N(A): monomials arise from [x_ij(a), x_jk(b)] = x_ik(ab) with i, j, k
    distinct, sums from products, negatives from inverses.
  - Tietze moves give a finite presentation on S.
- **Import (finite presentation).** `steinberg-finite-presentation-and-kazhdan-theorem` via its citation route
  `steinberg-finiteness-kazhdan-citation`. At review the EJZ statement was read verbatim from the arXiv e-print
  0809.4095v2, fetched on MSI (`EL_n0909.tex`, lines 2496–2501):
  > "By a theorem of Krstić and McCool [Theorem 3]{KrM}, the Steinberg group St_n(R) is finitely presented for any
  > n ≥ 4 and any finitely presented ring R, in particular for R = Z⟨x_1, …, x_d⟩. … By [Corollary 2]{KrM}, the group
  > St_3(R) is not finitely presented whenever R surjects onto F[t] for some field F."

  [KrM] is S. Krstić and J. McCool, *Presenting GL_n(k⟨T⟩)*, J. Pure Appl. Algebra 141 (1999) 175–183, DOI
  10.1016/S0022-4049(98)00022-X. The primary text was NOT obtained: ScienceDirect served a bot page, the Elsevier API
  needs a key, and Wayback returned 429. So the import stands on EJZ's explicit statement, as its citation route
  already records.
- **Step 3 (homomorphism).**
  - B contains θ of every prefix of every relator and of every u_c, of S, and 1. ψ(1) = 1, since ψ(1)² = ψ(1) in a group.
  - Prefix induction gives ρ(v) = ψ(θ(v)), using θ(v'), θ(s), θ(v's) ∈ B.
  - S is closed under inverses, so relators can be taken as positive words.
  - Each relator has θ(w) = 1, so ρ(w) = 1 and ρ descends to St_N(A) → Q.
- **Step 4 (level ideal).** Re-derived with [g, h] = ghg^{-1}h^{-1}.
  - a ∈ K_ij ⇒ ρ([x_ij(a), x_jk(1)]) = 1 ⇒ a ∈ K_ik. a ∈ K_jk ⇒ ρ([x_ij(1), x_jk(a)]) = 1 ⇒ a ∈ K_ik.
  - The displayed cycle K_12 ⊆ K_13 ⊆ K_23 ⊆ K_21 ⊆ K_31 ⊆ K_32 ⊆ K_12 checks link by link, and third indices connect
    all pairs.
  - [x_12(a), x_23(b)] = x_13(ab) makes K a two-sided ideal, of finite index since a ↦ ρ(x_13(a)) lands in finite Q.
  - 1 ∉ K because π(1) ≠ 0.
- **Step 5 (window).** For c ∈ D, ρ(x_13(c)) = ψ(θ(u_c)) = ψ(e_13(π(c))). Injectivity of ψ on B gives c ∈ K ⟺
  π(c) = 0. Injectivity, 0 and 1, negatives (via l(−r) + l(r) ∈ D) and window sums and products (via
  l(r+s) − l(r) − l(s) and l(rs) − l(r)l(s) ∈ D) all check.
- **Rank.** Steps 3–5 need only N ≥ 3, so N ≥ 4 enters only through the import. The method cannot give N = 3:
  A = Z⟨x_r⟩ surjects onto F_p[t], so St_3(A) is not finitely presented (KM Cor 2, as quoted by EJZ). Rank 3 is correctly
  not claimed.
- **No hidden hypotheses.** No countability, simplicity or finite generation of R is used.
- **Model tests.**
  - L_k(1,2): LEF rings are directly finite, so no EL_N(L_k(1,2)) with N ≥ 4 is LEF. This is consistent with tex Cor l.1016.
  - Group rings: consistent with `group-ring-lef-iff-group-lef-iff-elementary-group-lef` (PASS, part 1 §C2).
- **Subsumption scan** (untruncated: 38 claim or route files on LEF rings with elementary groups; 49 on finite
  presentation of Steinberg groups).
  - `cohn-elementary-group-is-not-lef` runs the same cover at one ring and is listed in `distinct_from`.
  - `non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra` consumes the rung and is consistent.
  - Nothing established asserts a ring that is not LEF with a LEF EL_N (N ≥ 4). No conflict.
- **Credit.** This is the ring form of "finitely presented LEF groups are residually finite", with the finitely
  presented cover from Krstić–McCool via EJZ. No novelty search was run by the lane or here.

## F2 `simple-lef-rings-are-exactly-matricial`: PASS, with a hypothesis GAP

- **Re-derived.**
  - Q_n ≠ 0 because φ_n is injective with φ_n(0) ≠ φ_n(1). J(Q_n) is proper.
  - Q_n/J(Q_n) is a nonzero finite semisimple ring. Wedderburn's little theorem makes it a product of M_d(F_q), and
    p_n onto one factor is unital.
  - ψ_n = p_n∘φ_n preserves window sums and products. Ψ = [ψ_n]_ω is a unital ring homomorphism with Ψ(1) ≠ 0, so its
    kernel is a proper ideal, hence 0.
- **GAP, hypothesis.** The proof uses an exhausting sequence W_1 ⊆ W_2 ⊆ … and a non-principal ultrafilter on N, which
  needs R countable. The claim node stated it for every simple LEF ring. Corrected at review to countable R, with a
  remark that the uncountable case holds with an ultrafilter on the directed set of finite windows. Corollary 3 and the
  merged node already assume countability.

## F3 merge: `lef-el-groups-force-exactly-matricial-simple-ring` marked ESTABLISHED: PASS, with a display GAP

- **Route `lef-el-groups-matricial-via-lef-ring`.**
  - `requires: [lef-elementary-groups-force-lef-rings, simple-lef-rings-are-exactly-matricial]`, both now PASS.
  - The claim's hypothesis (EL_N LEF for every N ≥ 3) includes N = 4, and the conclusion follows over finite fields,
    which is stronger than stated.
- **Equivalence remark.** (c) ⇒ (d) over finite fields needs only that countable subgroups of algebraic ultraproducts of
  finite groups are LEF, which is elementary. It does not depend on the unreviewed Malcev step of
  `exactly-matricial-rings-have-lef-general-linear-groups`.
- **Root display.** `kazhdan-elementary-approximation-type-mirrors-ring-type` lists this node as (L⇒). That is
  consistent.
- **GAP, display.** The title was still the open question ("… is the ring exactly matricial?") while the body reads
  ESTABLISHED. It is replaced at review by a declarative title matching the body; the id is unchanged.
