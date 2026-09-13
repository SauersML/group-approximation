---
rg: 2
id: ample-steinberg-el-simple-mod-centre-without-hausdorff
kind: claim
title: EL_n over a simple Steinberg algebra is simple modulo its centre, with no Hausdorff hypothesis on the groupoid
distinct_from:
  steinberg-elementary-groups-are-simple-mod-centre: that assumes a Hausdorff minimal effective groupoid and identifies the centre as k^×; this drops Hausdorffness, assumes only that A_k(𝒢) is simple, and does not identify the centre.
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `𝒢` an ample groupoid, not necessarily Hausdorff, with compact,
infinite, Hausdorff unit space, such that `A = A_k(𝒢)` is simple. For `n ≥ 3`:
- every normal subgroup of `EL_n(A)` is central or all of `EL_n(A)`;
- `S_n = EL_n(A)/Z(EL_n(A))` is an infinite simple group;
- if `k` is finite and `A` is finitely generated as a ring, `S_n` has property (T).

Why: `A` is unital (`1 = 1_(𝒢⁰)`), so it is a simple ring. Local annihilation needs no Hausdorffness. The Lean ring
criterion then gives simplicity, and `e_12(A)` injects into `S_n`. Artifact §2.

It applies to non-Hausdorff groupoids of self-similar actions whose Steinberg algebras are simple, e.g. the Grigorchuk
groupoid over any field of characteristic `≠ 2` (`grigorchuk-steinberg-algebra-simple-iff-char-not-two`), via the
Clark–Exel–Pardo–Sims–Starling criterion (`cepss-nonhausdorff-steinberg-simplicity`).

Route: `ample-steinberg-el-simple-mod-centre-without-hausdorff-proof`.

**Review (un-verify, 2026-09-13): PASS.** Local annihilation (part 1 §1) uses only that elements are finite combinations of `χ_B` and that the unit space is compact, infinite, Hausdorff and zero-dimensional, so it holds for non-Hausdorff `𝒢`; unital simple algebra gives `IsSimpleRing`; the Lean criterion, infiniteness and the (T) clause (finite `k`, finitely generated `A`) re-derived. See `research/artifacts/un-review-2026-09-13-part7.md` §1.
