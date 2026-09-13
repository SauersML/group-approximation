---
rg: 2
id: bernoulli-lifts-across-finite-kernels-force-virtual-splitting
kind: claim
title: Over a w-rigid quotient, a Bernoulli shift lifts to a free action across a finite kernel only if the extension virtually splits
distinct_from:
  finite-kernel-rokhlin-ascent-from-weakly-minimal-lift: that proves ascent when some Bernoulli shift of the quotient lifts; this shows that over w-rigid quotients such a lift exists only for virtually split extensions, where ascent is already a finite-index statement.
  finite-central-extension-rf-iff-virtually-splits: that decides residual finiteness of a finite central extension by virtual splitting; this shows that lifting one Bernoulli action forces the same virtual splitting over w-rigid bases.
  popa-bernoulli-cocycle-superrigidity: that is Popa's theorem for cocycles of malleable actions; this applies it to the lifting cocycle of an N-torsor over a Bernoulli shift.
---

**ESTABLISHED (unreviewed)** by [[bernoulli-lifts-across-finite-kernels-proof]].

Let `N ◁ W` be finite and `Q = W/N`. Suppose `Q` contains an infinite normal subgroup `H` with the relative
property (T), for instance an infinite property (T) group with `H = Q`. If some Bernoulli shift `L^Q` lifts, meaning
it is the `N`-quotient of a free p.m.p. `W`-action, then `π^-1(Q_0) = N ⋊ Q_0'` for some finite-index `Q_0 <= Q`
and a subgroup `Q_0' ≅ Q_0` of `W`. In other words, the extension splits over `Q_0`.

**Consequences.**
- **No Bernoulli lifting beyond the trivial cases.** Over w-rigid quotients, case (ii) of
  `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` applies only to virtually split extensions. There `W`
  contains `Q_0'` with finite index, and ascent follows from `bernoulli-rokhlin-maximality-passes-to-subgroups`.
- **Deligne's triple cover.** `Sp_4(Z)` has property (T), and `E_3` is not residually finite, so the extension is not
  virtually split (`finite-central-extension-rf-iff-virtually-splits`). So no Bernoulli shift of `Sp_4(Z)` is the
  `C_3`-quotient of a free `E_3`-action. The same holds for every s-malleable, weakly mixing free action covered by
  Popa's theorem.
- **What stays open.** Popa's theorem does not apply to the twisted section action `Ω/N`. Case (i) of the
  conditional ascent (weak containment of a liftable action in all free actions) is not excluded here.

**Model test.** Hypothesis side: `E_3 -> Sp_4(Z)` satisfies the hypotheses and is not virtually split, so the theorem
has content there. Conclusion side: the section action `Ω` of any extension is a free `W`-action whose quotient `Ω/N`
lifts without any splitting. That is consistent, because `Ω/N` is not s-malleable.
