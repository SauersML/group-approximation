---
rg: 2
id: smooth-design-rich-2to1-hardness
kind: claim
title: 2-to-1 games are NP-hard to approximate near 1 versus near 0 on instances with smooth low-degree pairing designs
distinct_from:
  rich-2to1-games-conjecture: that demands the uniform distribution on all perfect pairings at every left vertex; this only demands t-wise uniformity for every fixed t plus the pull-back density comparison, which admissible families of size about m^n n^O(t) satisfy, far below all (2n-1)!! pairings.
  noise-test-sound-on-smooth-design-rich-inputs: that is the proved transfer showing these properties suffice for the reduction; this is the open hardness hypothesis they feed.
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**OPEN.** The Smooth-Design Rich 2-to-1 Conjecture. There is a function
`C(K,m)` such that for every `epsilon > 0`, `t >= 1`, `m >= 2` and `K >= 1`,
for all sufficiently large `n`, `Gap-2-to-1_n[1-epsilon, epsilon]` is NP-hard on
instances whose pairing family at every left vertex is

* `t`-wise uniform: every partial matching of at most `t` pairs has its
  uniform-matching probability; and
* `(K,m,C(K,m))`-smooth: the pull-back distribution has density at most
  `C(K,m) m^(-2n)` at `K`-roughly balanced points.

Smoothness is required only for the one pair `(m,K)` that the reduction fixes
from `epsilon`. Requiring it for every `m` at once would force
`log |F| = omega(n)`, by `pullback-smoothness-needs-exponentially-many-pairings`.

With `noise-test-sound-on-smooth-design-rich-inputs` this implies UGC (route
`ugc-from-smooth-design-rich-2to1`). The Rich 2-to-1 conjecture, at all large
alphabet sizes as BKM's Section 5 uses it, implies it: all pairings form an
admissible family.

By `pullback-smoothness-needs-exponentially-many-pairings` an admissible family
has at least about `m^n` members, but it may be much smaller than the set of all
pairings: `smooth-pairing-designs-of-size-m-to-the-n-exist` gives admissible
distributions with support `m^n n^(O(t))`. The
point of this formulation: the outer PCP must realize a low-degree design with
a density comparison, not the uniform distribution.

## Attempts

* **Manufacture uniform pairings from unique games** (BKM Appendix B: right
  vertices `(v, sigma)` with `sigma` a random 2-to-1 map of the right alphabet).
  Gives full richness, but consumes a hard unique game, so it is circular as a
  hardness source. The outer-side lane `ugc-2` is testing what breaks on the
  proved 2-to-2 and 2-to-1 instances.
* **Refine the proved Grassmann 2-to-1 instances the same way.** Dies:
  composing a 2-to-1 projection with another 2-to-1 map gives a 4-to-1
  constraint.
* **Relabel labels per vertex or per edge.** Dies. A per-vertex relabeling
  conjugates the whole family, and per-edge conjugation is pure gauge
  (`edge-conjugation-of-2to1-constraints-is-pure-gauge`).
* **Use an algebraic family of subexponential size.** Dead: route
  `smooth-design-hardness-via-subexponential-families`, killed by
  `pullback-smoothness-needs-exponentially-many-pairings`. For separated
  families the test itself also fails
  (`separated-small-pairing-families-defeat-the-noise-test`).
* **Keep the matchings learnable.** On such instances the test is no more sound
  than the derived unique game (`derived-unique-game-lower-bounds-the-noise-test`),
  so the hardness would have to come from a unique game already
  (`bkm-test-transparent-on-learnable-games`). The barrier does not reach
  generic admissible families: random exponential families are unlearnable
  even by list decoders (`random-exponential-pairing-families-are-unlearnable`).
  It still acts through every decodable *feature* of the matching
  (`noise-test-transparent-on-decodable-matching-features`). So an outer
  construction that keeps an ancestral feature recoverable, such as an `F_lin`
  direction, needs the split game to be hard on its own.
* **Open.** A new outer construction whose left vertices see exponentially many
  kernel partitions forming a smooth `t`-wise uniform family, while keeping the
  soundness of the proved 2-to-1 theorem. None is supplied.
