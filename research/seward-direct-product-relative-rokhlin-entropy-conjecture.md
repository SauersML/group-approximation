---
rg: 2
id: seward-direct-product-relative-rokhlin-entropy-conjecture
kind: claim
title: For free actions X and Y, the Rokhlin entropy of X times Y relative to Y equals the Rokhlin entropy of X
distinct_from:
  seward-weak-containment-relative-entropy-equality: that proves the equality when Y is weakly contained in all free actions; this is the equality for every pair of free actions, which Seward records as open over nonamenable groups.
  rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded: that reduces ascent across a finite kernel to the entropy of one specific product over the quotient; this conjecture would supply that entropy on every group.
---

**OPEN.** Let `G` be countably infinite and let `G ↷ (X, μ)` and `G ↷ (Y, ν)` be free p.m.p. actions. Then

    h_G(X × Y, μ × ν | B(Y)) = h_G(X, μ).

The inequality `<=` always holds, since a generator of `X` generates `X × Y` relative to `B(Y)`.

**Source.** B. Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2, introduction, read on 2026-09-13
from the PDF text on MSI: "A natural conjecture is that in the case of direct product joinings we have
hG(X×Y;µ×ν|B(Y)) = hG(X;µ) for all free actions G y (X;µ) and G y (Y;ν). This is known to hold when G is amenable
but is unknown otherwise."

**Consequences in the graph.**
- **Finite kernels.** Over a finitely generated Rokhlin-maximal `Q`, it gives maximality of every finite extension
  of `Q` (`finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`, case (iii)). So it implies
  `rokhlin-maximality-ascends-finite-normal-extensions`.
- **Finite-index subgroups.** Seward's Theorem 1.6 there says that equality for all finitely modular `Y` is
  equivalent to the subgroup formula for finite-index subgroups. That theorem is not imported here.

## Attempts

- **Weak containment (Seward, arXiv:1602.06680v2, Theorems 1.2 and 6.5).** The equality holds when `Y` is weakly
  contained in all free actions.
  - The proof takes a factor `Z` of `X` with small Rokhlin entropy and the same stabilizers.
  - It uses the weak containment of joinings `X × Z ≽ X × Y` (his Corollary 5.2), and the fact that relative
    Rokhlin entropy can only decrease along such weak containments (his Corollary 6.4(4)).
  - It dies when `Y` is not weakly contained in all free actions.
  - The pairs needed for finite-kernel ascent have `Y = Ω/N`, the twisted section action of a finite extension.
    There weak containment asks for an approximate trivialization of the extension class on Bernoulli orbit
    relations (`research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md`, Section 5).
