---
rg: 2
id: hyperbolic-f3-by-z-family-with-genus-two-surfaces
kind: claim
title: Infinitely many non-isomorphic hyperbolic F_3-by-Z groups contain genus-two surface subgroups, all certified by one legal f-folded fatgraph
distinct_from:
  hyperbolic-f3-by-z-with-genus-two-surface-certificates: that certifies two explicit automorphisms and their 22 relabelled variants; this reuses one pairing for an infinite two-parameter family, whose mapping tori have unbounded torsion in H_1 and so fall into infinitely many isomorphism classes.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the criterion; this is an infinite class of hyperbolic groups where the criterion applies.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this covers an infinite family of hyperbolic free-by-cyclic groups, a class listed there as uncovered.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/family_certificates.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/family_phi1_len7.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi1028.json
---

**ESTABLISHED** (proof in `hyperbolic-f3-by-z-family-with-genus-two-surfaces-proof`; the
certificate step is computer-checked once, the rest is closed-form).

Let `F = F(a, b, c)`. Put `X = ca` and `Y = babb`. Let `w` be a positive word in `X, Y` that is
empty or ends in `Y`, and let `i` and `j` be the numbers of `X` and `Y` in `w`. Define

```text
phi_w : a -> abb . w(ca, babb),   b -> ca,   c -> babb.
```

Then:

1. `phi_w` is a positive automorphism of `F`. Its characteristic polynomial is
   `t^3 - (i+j+1) t^2 - (i+3j+5) t + 1`.
2. `G_w = F x|_{phi_w} Z` is a one-ended hyperbolic group.
3. `G_w` contains the fundamental group of the closed orientable surface of genus 2.
4. The torsion subgroup of `H_1(G_w)` has order `2(i + 2j + 2)`. So every even order `>= 4` occurs,
   and among the `G_w` there are infinitely many isomorphism classes.

For `w` empty this is `phi_1` of `hyperbolic-f3-by-z-with-genus-two-surface-certificates`.

## Why the certificate does not see `w`

- The certificate of `phi_1` (in `surface_phi1028.json`) has `partial^- = {bc, BC}`. Its data depend on
  `phi(b)` and `phi(c)` only: the boundary words, their labels, and the positions of the
  `f`-corners.
- Condition (L) also needs the gates of `phi`. These depend only on the first and last letters of
  `phi(a)`, `phi(b)` and `phi(c)`.
- For every `w` above, `phi_w(a)` starts with `a` and ends with `b`, just as `phi_1(a) = abb` does.
- So the same 16-letter pairing is a legal `f`-folded fatgraph with `chi = -2` for every `phi_w`.

`family_certificates.py` re-runs the independent checker on that unchanged pairing for all 128
words `w` of length `<= 7`. It also checks each explicit inverse and the closed form of the
characteristic polynomial. Result: 128 of 128 pass (`family_phi1_len7.log`).

## Why it matters

The target `one-ended-hyperbolic-groups-contain-surface-subgroups` lists hyperbolic free-by-cyclic
groups as a first uncovered class. Before this node, main had no certificate for any of them
(`automorphism-immersion-representatives-have-finite-order` kills Calegari--Walker's immersion
route).

This node gives an infinite, explicitly parametrised family of such groups with genus-two surface
subgroups. The proof is a single finite pairing plus closed-form algebra.

The endomorphism hypothesis of the legal criterion is local to the letters on `partial^-`. The
free letter `a` can carry any right multiplier from `<phi(b), phi(c)>` that ends in `Y`. That is
the mechanism, and it should transfer to other certificates.

**Literature scope.** Brady and coauthors (Geom. Dedicata 2006, second-hand only) report hyperbolic
free-by-cyclic groups with surface subgroups. No source was checked for an infinite family of
this kind. So the novelty claim is about the route and the family, not about existence.
