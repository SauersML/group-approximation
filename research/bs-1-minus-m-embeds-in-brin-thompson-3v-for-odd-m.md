---
rg: 2
id: bs-1-minus-m-embeds-in-brin-thompson-3v-for-odd-m
kind: claim
title: For every odd m >= 3 the Baumslag-Solitar group BS(1,-m) embeds in the Brin-Thompson group 3V
requires:
  - odd-smart-induced-map-has-height-m-renormalization
  - renormalizable-thompson-elements-give-negative-baumslag-solitar
distinct_from:
  bs-1-m-embeds-in-brin-thompson-3v-for-odd-m: that is BS(1,m); this is BS(1,-m), whose generator is conjugate to the inverse of its m-th power.
  bs13-embeds-in-brin-thompson-3v: that is BS(1,3); the case m = 3 here is BS(1,-3).
---

**ESTABLISHED** (lane bh-free-18, lane proof, not reviewed). No priority claimed: the bounded arXiv
queries of 09-18 found no `BS(1,n)`, `|n| >= 2`, in any untwisted `nV`.

**Proof.** Fix odd `m >= 3`.
- `odd-smart-induced-map-has-height-m-renormalization` gives `U' ∈ 2V` with a height-`m` renormalization.
  For `m <= 11` it is also machine-certified (`research/artifacts/gq-bh-bh-free-18-odd-smart-certificate.md`).
- `renormalizable-thompson-elements-give-negative-baumslag-solitar` with `k = 2` gives `s, t ∈ 3V` with
  `t s t^-1 = s^-m` and `⟨s, t⟩ ≅ BS(1,-m)`. ∎

**Remarks.**
- The same `s` also gives `BS(1,m) = ⟨s, u⟩`, so both lie in one 3-generated subgroup `⟨s, u, σ × id⟩ ≤ 3V`.
- `BS(1,-1)`, the Klein bottle group, already lies in `V` (main records `BS(m,±m) ≤ V`). Only `|m| >= 2` is new.
- Even `m`, and `BS(1,2)` in particular, remain open (`bs12-embeds-in-brin-thompson-2v`).
