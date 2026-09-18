---
rg: 2
id: fpbs-relative-fixed-price-fg-pairs
kind: claim
title: For a free action of a finitely generated group, the relative cost over an infinite finitely generated subgroup is at most the positive part of the cost difference
distinct_from:
  fpbs-relative-fixed-price-free-pairs: that is the special case of free pairs, where the costs are ranks and the statement needs no fixed price hypothesis to be read; this is the general finitely generated statement used against shape (B) of Theorem G.
  fpbs-infinite-contact-zero-relative-cost: that proves relative cost 0 under infinite contacts; this asks for a cost-difference bound for every pair, and its content is in the finite-contact (malnormal) case.
  fpbs-mal-bernoulli-single-stage-floor: that is a conjectured positive floor at one malnormal pair; this claim implies its negation.
  fpbs-relative-stage-costs-bound-cost-by-stage-liminf: that is the ESTABLISHED lemma turning this inequality along a chain into a total-cost bound.
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

**OPEN.** Let `K ≤ L` be finitely generated groups with `K` infinite, and let
`a` be a free p.m.p. action of `L`. Prove

```text
relC( E_{a|L} ; E_{a|K} ) ≤ ( C(E_{a|L}) − C(E_{a|K}) )^+ .
```

The reverse inequality `relC ≥ C(E_{a|L}) − C(E_{a|K})` always holds. So the
claim says the relative cost is exactly the cost difference, or 0 when `K`
costs at least as much as `L`.

**Known cases** (artifact §2.2):
- `K` amenable, or `C(E_{a|L}) = 1`, by Ershov–Golan–Sapir Lemma 5.7;
- `K` normal, commensurated, or of finite index, or more generally infinite
  contacts;
- free factors.

The content is in malnormal pairs with `C(K) ≥ C(L)`, where the claim predicts
relative cost 0. The ESTABLISHED finite-contact, linear-perimeter and
packing-floor obstructions rule out only *packing* certificates of that.

**Why it matters** (artifact §3.3). Under fixed price for finitely generated
groups, this claim and `fpbs-relative-stage-costs-bound-cost-by-stage-liminf`
give `C(a) ≤ c*(Γ)` for every free action of every countable group that is
not locally finite. So shape (B) of Theorem G can occur only with
`c* = ∞`.

**How it can fail.** A finite-contact pair `K ≤ L` with `C(K) ≥ C(L)` and a
free action with a positive relative floor. At
`(F_2, <a, bab^{-2}>)` and the Bernoulli shift of `Γ_mal` restricted to a
stage, such a floor is exactly `fpbs-mal-bernoulli-single-stage-floor`.

## Attempts

**Derivations from fixed price for finitely generated groups (September 17,
2026; artifact §4).** None of these gives the claim:
- the double `L *_K L`, since no amalgam cost formula exists over
  non-amenable `K`;
- the HNN extension centralizing `K`, which is circular;
- relative rank gradients and relative L2 invariants, which vanish.
