---
rg: 2
id: fixed-perfect-seeds-do-not-black-box-exactify-tv
kind: claim
title: A fixed perfect seed cannot black-box exactify the positive-noise TV test
artifacts:
  - research/fixed-perfect-seed-composition-no-go-proof.md
distinct_from:
  tv-central-flags-and-private-slacks-cannot-exactify: that treats finite accept blocks, central flags, and private slacks; this allows an arbitrary fixed infinite-dimensional perfect seed and proves a noncentral common-gate obstruction plus the finite-value dichotomy.
  taller-vidick-positive-noise-collapses-central-sign: that isolates the opposite-sign equation pair; this classifies standard black-box ways of wiring another perfect game to that pair.
  nested-conjugacy-stops-at-tv-dictator-projectors: that treats the zero-noise BCS-to-LCS boundary; this treats attempts to repair positive-noise completeness by composition with a pre-existing perfect seed.
---

Let \(T_\epsilon\), with \(\epsilon>0\), be the positive-noise
Taller--Vidick LCS test, and let \(S\) be any fixed finite game with a
perfect commuting-operator strategy.  Write \(\omega_q\) for the supremum
over finite-dimensional strategies.

None of the standard black-box compositions produces a new perfect
commuting-versus-finite gap.

1. A positive-probability mixture which retains \(T_\epsilon\) unchanged,
   or a parallel AND product with \(T_\epsilon\), cannot be perfect in the
   commuting model: a perfect composite restricts to a perfect strategy for
   \(T_\epsilon\), but its support contains the same-left-side,
   opposite-right-side equation pair.

2. More strongly, suppose one fixed seed operator \(F\) gates both members
   of that pair, on the left, right, or by compression.  In a \(J=-I\)
   representation the two gated equations imply \(F=0\).  This uses no
   commutation between \(F\) and the source variables.  Thus even a
   noncentral common seed flag has zero active support.

3. An OR or bypass composition which accepts whenever the seed accepts has

   $$
   \omega_q(T_\epsilon\mathbin{\mathrm{OR}}S)
   \geq \omega_q(S).
   $$

   If \(\omega_q(S)=1\), the composite has no finite-dimensional value gap.
   If \(\omega_q(S)<1\), then \(S\) itself already has perfect commuting
   value and a finite-dimensional gap; the desired ingredient was assumed,
   not constructed.

Hence a fixed seed with only nonattainment of finite-dimensional
perfection cannot exactify the TV reduction by AND, OR, positive mixture,
direct sum, or a common compression.  A live construction must instead use
different source-dependent noncommuting gates for different relations and
prove a reverse finite-dimensional decoder.  This claim does not rule out
that non-black-box possibility and does not construct a nonhyperlinear
group.
