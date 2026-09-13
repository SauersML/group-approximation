---
rg: 2
id: subexponential-growth-simple-algebras-have-rank-models
kind: claim
title: Every simple affine algebra of subexponential growth has a unital rank model over its base field
---

**ESTABLISHED (unreviewed).** Let `k` be any field and `R` a simple unital affine `k`-algebra of
subexponential growth (for instance of finite Gelfand–Kirillov dimension). Then `R` has a unital rank model
over `k`, carries a faithful Sylvester matrix rank function, and is stably finite.

This is `simple-amenable-affine-algebras-have-unital-rank-models` combined with Elek's (E4), "any affine
algebra of subexponential growth is amenable".

**Scope and boundary.** The converse fails: amenable algebras of exponential growth exist (`k[Γ]` for any
amenable `Γ` of exponential growth), so subexponential growth is a sufficient criterion only. Nothing here
gives exact matricial models, which are strictly stronger; see
`simple-rings-with-local-matrix-models-are-matricial`.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §2.2): PASS.** A routine
combination of Elek, arXiv:math/0203261 Proposition 4.1, with Arzhantseva–Păunescu, arXiv:1212.6780v1 Corollary 11.15
(credited on the required claim).
