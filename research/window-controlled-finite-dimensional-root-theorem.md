---
rg: 2
id: window-controlled-finite-dimensional-root-theorem
kind: claim
title: Finite-dimensional roots that stay inside a prescribed multiplicativity window
distinct_from:
  finite-window-decoder: that asks for a common finite label space on which the four one-sided Leavitt maps act with vanishing boundary and pairing error -- a decoder for one specific algebra; this asks for a solution of a group equation in finite dimensions whose evaluation path stays inside a control window, for an arbitrary group. Both say "window" and nothing else is shared.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The statement that would extend the hyperlinear proof to all groups.  For
every group `G`, every finite `F <= G \ {1}`, every nonsingular
`w in G * <t>` and every `eps > 0` there are `n`, a map `rho` from a finite
window `W <= G` containing `F` and every coefficient of `w` into `U(n)`, and
`T in U(n)`, such that

* `rho` is `eps`-multiplicative on `W` and `eps`-separating on `F`, in a
  metric whose null sequences form a **conjugation-stable two-sided ideal**;
* `w(rho, T) = I`, or `eps`-close to it;
* every intermediate product encountered while evaluating `w` on `W` remains
  inside the region on which the two properties above are asserted, with
  bounds independent of `n`;

and the bounds are uniform enough for an ultraproduct to exactify.  Then
`kervaire-laudenbach-nonsingular-conjecture` follows, by
`kl-via-window-controlled-roots`.

## Attempts

None run here.  The value of the node is the list of ways the obvious
readings collapse, all of which are recorded rather than attacked.

1. **Read the metric as normalized Hilbert--Schmidt.**  Then the first bullet,
   quantified over all finite windows, *is* hyperlinearity, and the lane
   proves exactly `kervaire-laudenbach-holds-for-hyperlinear` — which this
   graph already has.  Stated this way the claim is not a generalization; it
   is the theorem plus the assumption that every group is Connes-embeddable,
   which is a strictly larger open problem and one this program is elsewhere
   trying to refute.  Any honest version of this lane must therefore work in
   a metric that arbitrary groups are known to carry.
2. **Weaken to point-strong approximation.**  Loses the third bullet: a root
   produced by a finite-dimensional degree argument can move test vectors out
   of the window, and the next coefficient is then evaluated where nothing
   was prescribed.  This is the specific gap, and it is a gap rather than a
   refutation — no theorem says such roots must escape.
3. **Weaken the trace to a general state.**  Loses the first bullet: for a
   state `phi`, the null sequences of `‖x‖_{2,phi} = phi(x*x)^{1/2}` need not
   form a two-sided ideal, nor be stable under conjugation by the root
   sequence, so the ultraproduct need not be a group quotient compatible with
   the coefficients.  Again "need not", not "does not"; a state with the
   required stability would revive the lane.

Traciality is not decoration in the hyperlinear argument — it is what makes
attempts 2 and 3 unnecessary there.  Whoever attacks this claim should decide
first which of the three bullets they intend to buy, and from what.

## Relation to the rest of this region

Independent of the reduction chain: it attacks
`kervaire-laudenbach-nonsingular-conjecture` directly and never passes
through the simple-group form, so it is unaffected by
`degree-kernel-abelianization-is-infinite-cyclic` and by the normal-rank
lane.  It is also the only lane here that would, if it succeeded, close the
conjecture without ever mentioning normal generation.
