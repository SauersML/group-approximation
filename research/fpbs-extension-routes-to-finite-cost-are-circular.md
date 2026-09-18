---
rg: 2
id: fpbs-extension-routes-to-finite-cost-are-circular
kind: claim
title: The minimal cost over free extensions of any free action is the group cost, so certifying finite cost through extensions is circular
distinct_from:
  fpbs-factor-invariance-equals-fixed-price: that is the equality sector (all free actions have equal cost iff every free factor map preserves cost); this is the finiteness sector that node leaves uncovered. Finite cost of all free actions is equivalent to descent of finiteness along product projections, and every infinite-cost action is the base of a factor map from an action of cost C(Gamma).
  fpbs-bernoulli-noise-does-not-change-cost: that is the identity C(a x s) = C(a) for Bernoulli noise over finitely generated groups; this is the unconditional identity min over all free extensions of b of their cost equals C(Gamma), for every countable group, together with the class kill it implies.
  fpbs-malnormal-subgroup-relations-finite-contacts: that kills base-measurable repair anchored in almost malnormal subgroup orbit relations; this kills the complementary class of extension certificates, at descent along factor maps with non-atomic fibres.
artifacts:
  - research/artifacts/fpbs-extension-certificates-carry-no-cost-information-2026-09-17.md
---

Let `Gamma` be a countably infinite group with `C(Gamma) < infinity`, and
let `b` be a free p.m.p. action.

1. Every free extension `e -> b` has `C(e) <= C(b)`, and
   `min { C(e) : e a free extension of b } = C(Gamma)`. The minimum is
   attained by `b x a_0`, where `a_0` is a free action of cost `C(Gamma)`.
2. The following are equivalent:
   - (U) every free action has finite cost;
   - (D_prod) `C(b x c) < infinity` implies `C(b) < infinity`, for all free
     `b`, `c`;
   - (D_ext) descent of finiteness along every factor map of free actions.
3. **Class kill.** Consider any route that builds an extension `e -> b` with
   a property `P` satisfied by `b x a_0 -> b`, certifies `C(e) <= K` with
   `K >= C(Gamma)`, and descends to `b`. Its descent step is equivalent to
   (U).
   - `a_0` can be taken mixing, so `P` may include products, relatively
     independent joinings, relative mixing and non-atomic fibres.
   - This covers products with auxiliary actions and Bernoulli noise,
     coinduction through finitely generated overgroups followed by
     restriction, and measure-equivalence transfer.
   - The invariant is the cost of a free extension. The dying step is
     descent along non-atomic fibres. Uniform finite fibres do descend
     (`research/artifacts/fpbs/docs/finite-fiber-cost-descent.md`, (1)).
4. **For `Gamma_mal`.** Coinduction to its ascending HNN overgroup `M` needs
   two descents:
   - from `M`-cost to `Gamma_mal`-cost, which fails for finiteness in
     general (`F_inf x Z`);
   - from a product of twists of `b` to `b`, which is (U) itself.

Status records a written deduction over the lifting inequality ([G00] Prop
VI.21, traffic document (1.1)) and attainment of `C(Gamma)` ([G00] Prop
VI.21). It is not independent validation.
