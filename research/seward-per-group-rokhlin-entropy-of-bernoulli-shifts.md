---
rg: 2
id: seward-per-group-rokhlin-entropy-of-bernoulli-shifts
kind: claim
title: Per group, the Rokhlin entropy of a Bernoulli shift is the smaller of its base entropy and the group's Rokhlin supremum
distinct_from:
  every-group-has-positive-rokhlin-entropy-action: that is the open existence hypothesis over all groups; this is Seward's per-group computation, valid for every countably infinite group without that hypothesis.
  bernoulli-shift-entropy-classifies-for-every-group: that is the open isomorphism classification of Bernoulli shifts by base entropy; this computes their Rokhlin entropy through one invariant of the group.
---

**ESTABLISHED (import).** Let `G` be a countably infinite group, and put

```text
h_sup(G) = sup { h^Rok_G(X,mu) : G acts freely, ergodically, p.m.p., with h^Rok_G(X,mu) < infinity }.
```

For every standard probability space `(L,lambda)`:

1. If `H(L,lambda) < ∞`, then `h^Rok_G(L^G,lambda^G) = min{ H(L,lambda), h_sup(G) }`.
2. If `H(L,lambda) = ∞`, then `h^Rok_G(L^G,lambda^G)` is `∞` when some free ergodic
   p.m.p. action of `G` has positive Rokhlin entropy, and `0` otherwise.
3. If a countable group `P` contains arbitrarily large finite subgroups and
   `h_sup(G) < ∞`, then `h_sup(P × G) = 0`.
4. If `G` is sofic, then `h^Rok_G(L^G,lambda^G) = H(L,lambda)`.
5. If `h^Rok_G(k^G,u_k^G) = log k` for every `k`, then `G` satisfies Gottschalk's
   surjunctivity conjecture and Kaplansky's direct finiteness conjecture.

Seward's per-group labels:
- **INF(G):** `h_sup(G) = ∞`.
- **POS(G):** some free ergodic action of `G` has positive Rokhlin entropy.
- **RBS(G):** `h^Rok_G(L^G,lambda^G) = H(L,lambda)` for every base.
- **INV(G):** base entropy is an isomorphism invariant of Bernoulli shifts over `G`.
- **CPE(G), GOT(G), KAP(G):** completely positive Rokhlin entropy of Bernoulli shifts,
  Gottschalk, and Kaplansky direct finiteness for `G`.

With these labels, `INF(G) ⇒ RBS(G) ⇒ INV(G) + CPE(G) + GOT(G) + KAP(G)` for each
single group, and `(∀G POS) ⇒ (∀G INF)` through the auxiliary groups `P × G`. For
one group, POS(G) ⇒ INF(G) is not known.

**Source.** B. Seward, *Krieger's finite generator theorem for actions of
countable groups II*, arXiv:1501.03367v4 (7 Apr 2019). Read on 2026-09-12 from
the PDF text extracted on MSI (`review-lit/entropy/1501.03367.txt`). Verbatim:
- Theorem 1.10: "Let G be a countably infinite group and let (L,λ) be a standard
  probability space with H(L,λ) < ∞. Then h^Rok_G(L^G,λ^G) = min{H(L,λ), h^Rok_sup(G)}."
- Theorem 1.11: "Let P be a countable group containing arbitrarily large finite
  subgroups. If G is any countably infinite group with h^Rok_sup(G) < ∞ then
  h^Rok_sup(P × G) = 0. Thus (∀G POS)⇒(∀G INF)."
- Theorem 1.12: "Let G be a countably infinite group and let (L,λ) be a standard
  probability space with H(L,λ) = ∞. Then h^Rok_G(L^G,λ^G) = ∞ if and only if there
  exists a free ergodic p.m.p. action G y (X,µ) with h^Rok_G(X,µ) > 0."
- Before Theorem 1.3: "When G is sofic, Rokhlin entropy is bounded below by sofic
  entropy [4, 2] and thus h^Rok_G(L^G,λ^G) = H(L,λ) whenever G is sofic."
- Corollary 4.1: "Let G be a countably infinite group. Assume that
  h^Rok_G(k^G,u_k^G) = log(k) for every k ∈ N. Then G satisfies Gottschalk's
  surjunctivity conjecture and Kaplansky's direct finiteness conjecture."
- End of Section 1: "INF⇒RBS⇒INV+CPE+GOT+KAP" and "(∀G POS)⇒(∀G INF)". After
  POS and INF are defined: "We do not know whether POS implies INF".

The proofs are not re-derived in this graph.
