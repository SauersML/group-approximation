---
rg: 2
id: ffz-rp-fpn-embedding-gives-fp-fn-embedding
kind: claim
title: "If every finitely generated recursively presented group embeds in a recursively presented group of type FP_n, every finitely presented group embeds in a group of type F_n"
distinct_from:
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that is an unconditional embedding statement, the conclusion of this implication at n = infinity; this is the implication itself, from recursively presented homological hosts to homotopical hosts
artifacts:
  - research/artifacts/zp-z1-01-ffz-fp3-level-three-2026-09-13-part1.md
---

Let `n ∈ N ∪ {∞}`. If every finitely generated recursively presented group
embeds into a recursively presented group of type `FP_n`, then every finitely
presented group embeds into a group of type `F_n`.

This is Theorem A of Francesco Fournier-Facio and Matthew C. B. Zaremsky,
*Finiteness properties and Higman's rope trick*, arXiv:2607.21727v1 (23 July
2026), quoted from the arXiv TeX source: "Let n ∈ N ∪ {∞}. If every finitely
generated recursively presented group embeds into a recursively presented
group of type FP_n, then every finitely presented group embeds into a group of
type F_n."

**Proof outline (from the source).** Let `U` be a universal finitely presented
group (Higman 1961) and `ι: U → H` an embedding into a recursively presented
group of type `FP_n`. The Higman embedding theorem and universality give an
embedding `ȷ: H → U`. The ascending HNN extension `E` of `U` along `ȷι` is
finitely presented. By Geoghegan–Mihalik–Sapir–Wise (Bull. London Math. Soc.
33 (2001), Lemma 3.1) it is also an ascending HNN extension of `ȷ(H) ≅ H`, so
it is of type `FP_n` (Bieri, *Homological dimension of discrete groups*, 2nd
ed., Proposition 2.12). A finitely presented group of type `FP_n` is of type
`F_n` (the source's Lemma 2.1). So `U ≤ E` with `E` of type `F_n`.

**What the proof uses.** Only one embedding of the single group `U` into a
recursively presented group of type `FP_n`. Such an embedding already gives
the stated hypothesis, since every finitely generated recursively presented
group embeds in a finitely presented group (Higman) and so in `U`. The level
`n = 3` is recorded as `universal-fp-group-embeds-in-an-rp-fp3-group` and
`every-finitely-presented-group-embeds-in-an-f3-group`; the level `n = ∞` is
the third equivalent form on `every-finitely-presented-group-embeds-in-an-f-infinity-group`.
