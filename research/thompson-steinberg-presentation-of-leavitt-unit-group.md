---
rg: 2
id: thompson-steinberg-presentation-of-leavitt-unit-group
kind: claim
title: Thompson's group V together with one transvection and ten relators presents the binary Leavitt unit group
distinct_from:
  leavitt-unit-group-steinberg-weyl-presentation: that is a seven-generator, sixty-relator presentation built on S_5 acting on a five-leaf chart; this has four generators and eighteen relators, with Thompson's V replacing S_5 and the letters absorbed into cone refinements.
  leavitt-unit-group-finitely-presented: that is bare finite presentability; this is a specific presentation whose ten non-V relators are indexed by cone configurations.
  bleak-quick-finite-presentations-of-thompson-v: that presents V alone; this adds one generator and ten relators to it and obtains a nonsofic group.
artifacts:
  - research/artifacts/thompson-steinberg-presentation-2026-09-12.md
  - experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_presentation.py
  - experiments/nonsofic-certificates/presentations/thompson-steinberg-presentation.json
  - research/artifacts/ex-review-presentations-2026-09-12-part2.md
---

**ESTABLISHED (2026-09-12)** through
`thompson-steinberg-presentation-of-leavitt-unit-group-proof`.

**Reviewed 2026-09-12 by `ex-verify-presentation`: completeness PASS**
(`research/artifacts/ex-review-presentations-2026-09-12-part2.md`, §3). The review rests on three inputs:
- the sixty-relator presentation;
- Bleak--Quick Theorem 2.1;
- their KBMAG statement that (2.4) and (2.3) have the same normal closure. That statement is published but
  was not reproduced. With (2.3) in place of (2.4), the same proof rests on Theorem 2.1 alone.

Two exposition gaps in Step 3, the `d = 1` cases of C1d and CEd, are closed in the review with one more
disjoint-cone commutation each.

Let `a, b, c` be Bleak--Quick's generators of `V` subject to their eight relators (2.4), and
adjoin one generator `x`. Write `{}^g x = g x g^-1`. The presented group

```text
Q = < a, b, c, x |  (2.4),
      x^2,   (a x)^3,
      [x, {}^(b^-1 a c b^-1 a b^-1) a],  [x, {}^(b^-1 a b^-1 c a b c) b],  [x, {}^(b^-1 a b^-1 c a b^-1) a],
      [x, {}^(b a b c a b^-1) x],   [x, {}^(b^-1) x],   [x, {}^(a b^-1 a) x],
      [x, {}^(a b^-1) x] = {}^(b^-1) x,
      {}^(c a b^-1 c a b^-1) x . {}^(c a b c a b) x = x  >
```

is isomorphic to `L_(F_2)(1,2)^x`. The isomorphism sends `a -> U_(00 01)`,
`b -> U_(01 10 11)^-1`, `c -> U_(1 00)` (maps on the right, `U_g e_w = e_(w.g)`) and
`x -> 1 + S[00]T[01]`. There are eighteen relators, of total length 322 and maximal length 37.

In words: **the first nonsofic group is Thompson's V with one involution glued in by ten
relations.**
- The three (H) relators say that `x` commutes with the copy of `V` on the cone `1`.
- (B) gives three commutations: disjoint cones, same source, same target.
- (C) is one Steinberg law, `[1+S[00]T[01], 1+S[01]T[10]] = 1+S[00]T[10]`.
- (Q) is one splitting, `1+S[00]T[01] = (1+S[000]T[010])(1+S[001]T[011])`.
- `(ax)^3` is the Weyl link.

Every other Steinberg relation, and every letter of the Leavitt algebra, comes from transporting
these by `V` and refining cones. The proof is a Tietze comparison with
`leavitt-unit-group-steinberg-weyl-presentation`. Surjectivity comes from the simplicity of `V`.
Every relator was checked exactly in `L^x`.

## Attempts

1. **Design (2026-09-12).** First landed as an open claim with three generators planned. Carried
   out with four generators: `V` enters through Bleak--Quick (2.4). A three-generator variant
   through their Theorem 1.3 has the same proof, with conjugators written in `u, v`; its word
   search was run separately.
