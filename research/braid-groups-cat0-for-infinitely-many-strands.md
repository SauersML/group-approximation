---
rg: 2
id: braid-groups-cat0-for-infinitely-many-strands
kind: claim
title: For infinitely many n the braid group B_n is CAT(0)
distinct_from:
  every-braid-group-is-cat0: that claim asks for a geometric action on a complete CAT(0) space for every n; this one asks only for infinitely many n. It is formally weaker, and equivalent to that claim given `braid-cat0-passes-to-fewer-strands`
  braid-groups-on-at-most-six-strands-are-cat0: that claim records the finitely many cases n <= 6 proved in the literature; this one needs an unbounded set of n
---

For infinitely many `n ≥ 1`, the braid group `B_n` acts properly and cocompactly
by isometries on a complete CAT(0) space.

**Why this is the right hole.** By `braid-cat0-passes-to-fewer-strands`, the
set of `n` with `B_n` CAT(0) is an initial segment of the positive integers. So
this claim is equivalent to `every-braid-group-is-cat0` (route
`every-braid-group-cat0-from-infinitely-many-strands`). A proof may choose any
unbounded family of `n`, for example `n = 2^k`, and it never has to treat the
intermediate `n`.

## Attempts

- **Orthoscheme route, one `n` at a time.** The dual braid complex of T. Brady,
  with the orthoscheme metric of Brady–McCammond (arXiv:0909.4778), is CAT(0)
  for `B_n` once the diagonal links of `|NCP_m|` are CAT(1) for all `m ≤ n`
  (route `every-braid-group-is-cat0-via-diagonal-links`). This is known for
  `n ≤ 6` (Haettel–Kielak–Schwer, arXiv:1304.5990v2, Theorem 4.17) and `n = 7`
  (Jeong, arXiv:2009.09350v1, Corollary 14).
  - *Where it dies.* The Brady–McCammond criterion for `n` already needs every
    `m ≤ n`, so a special family of `n` gives no shortcut on this route.
  - The turning-face search of `noncrossing-partition-diagonal-links-are-cat1`
    leaves 22268 candidate chains at `n = 8`. So the method as stated does not
    reach `n = 8`.
- **Downward transfer (2026-09-16).** `braid-cat0-passes-to-fewer-strands`
  proves `B_{n+1}` CAT(0) ⇒ `B_n` CAT(0), using the centralizer
  `C_{B_{n+1}}(Δ²_n) = B_n × Z` and splitting off a central `Z`.
  - *Where it dies.* It only goes downwards and builds no space for `n ≥ 8`.
    Proposition G extracts smaller groups from centralizers and builds no space
    for a larger group. We know no gluing principle that builds a space for
    `B_{n+1}` from one for `B_n`.
- **Ambient groups (idea, not pursued).** By the general form in
  `braid-cat0-passes-to-fewer-strands` (artifact, Proposition G): let `G` be
  CAT(0), and suppose that for infinitely many `n` some element of `G` has
  centralizer `H_n × Z` with `H_n ≅ B_n`. Then this claim follows.
  - *Where it dies.* Any such `G` is at least as hard, and no candidate was
    found. The obvious hosts of braid groups, mapping class groups of closed
    surfaces of genus `≥ 3`, are not CAT(0) (Kapovich–Leeb; Bridson; not
    re-read here).
