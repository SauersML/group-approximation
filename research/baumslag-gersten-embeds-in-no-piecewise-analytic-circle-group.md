---
rg: 2
id: baumslag-gersten-embeds-in-no-piecewise-analytic-circle-group
kind: claim
title: Every homomorphism from the Baumslag–Gersten group to a group of piecewise real-analytic circle homeomorphisms kills a, so its image is cyclic
distinct_from:
  baumslag-gersten-embeds-in-no-graph-almost-automorphism-group: that excludes zero-dimensional almost-automorphism hosts through equicontinuity; this excludes one-dimensional piecewise-analytic hosts, which contain BS(1,2) with a parabolic and are not reached by any equicontinuity argument.
  baumslag-gersten-equicontinuous-generator-acts-trivially: that concerns actions on compact zero-dimensional spaces in which a is equicontinuous; this concerns circle actions by piecewise-analytic homeomorphisms, where a is not assumed equicontinuous.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Statement.** Let `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`, and
let `PA(S^1)` be as in `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`.
Every homomorphism `ρ : BG → PA(S^1)` has `ρ(a) = 1`, so `ρ` factors through
`BG / <<a>> ≅ Z`, and `ρ(BG)` is cyclic.

**Consequences.** `BG` embeds in no subgroup of `PA(S^1)`. That excludes:
- every group of PL circle homeomorphisms with finitely many breakpoints;
- every group of piecewise-`PSL_2(R)` homeomorphisms of `RP^1` with finitely
  many breakpoints, among them Thompson's `T` and Lodha's finitely presented
  infinite simple group `S` (arXiv:1710.06220v2, Theorem 1.1);
- the analogous groups on `[0,1]`, and on the line with projective ends.

**Relative to BS(1,2).** In PL groups, including Thompson's `T` in its PL model, one square relation already
suffices. By Item 2 of `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`,
an element conjugate to its square is tangent to the identity at the ends of its
gaps. A PL piece of slope `1` at a fixed point is the identity near it, so the
element is trivial and `BS(1,2)` does not embed (compare
`bs-1-n-does-not-embed-in-pl-plus-interval`). So for PL hosts this claim adds nothing
beyond `BS(1,2)`. It is new for hosts that contain `BS(1,2)`, such as Lodha's `S`:
`BB(1,2) < S`, and `BS(1,2) = < η, ν_1 ν_2 > ≤ BB(1,2)` (arXiv:1710.06220v2, Corollary 5.3 and §2.7,
read from the PDF text).

**Sharpness.** `BS(1,2) = < a, b >` embeds in `PSL_2(R)` through `a(x) = x+1` and
`b(x) = 2x`. So the stable letter `t` is essential. It makes `b` conjugate to its
own square, and that forces `b` to be tangent to the identity at its fixed points.

**Not covered.**
- Circle actions by homeomorphisms that are not piecewise analytic, such as
  countably many breakpoints or `C^∞` germs flat at a fixed point.
- Cantor-space hosts outside the almost-automorphism groups of finite graphs:
  Brin--Thompson `nV`, rational similarity groups, twisted Brin--Thompson groups
  and shell envelopes.

The proof is `baumslag-gersten-piecewise-analytic-circle-obstruction-proof`.
