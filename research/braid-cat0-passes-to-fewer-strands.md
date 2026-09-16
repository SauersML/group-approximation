---
rg: 2
id: braid-cat0-passes-to-fewer-strands
kind: claim
title: If the braid group B_{n+1} is CAT(0), then so is B_n
artifacts:
  - research/artifacts/braid-cat0-fewer-strands-2026-09-16.md
---

**Statement.** Let `n ≥ 1`. Suppose `B_{n+1}` acts properly and cocompactly by
isometries on a complete CAT(0) space. Then `B_n` acts properly and cocompactly
by isometries on a complete CAT(0) space.

Proved by `braid-cat0-passes-to-fewer-strands-proof`. Full details are in the
artifact.

**General form.** Let `G` act geometrically on a complete CAT(0) space. If an
element `γ ∈ G` has centralizer `C_G(γ) = H × ⟨z⟩` with `z` of infinite order,
then `H` is CAT(0). More generally, if `z` is central of infinite order in a
CAT(0) group `G`, then `G/⟨z⟩` is CAT(0). For braids, take `γ = Δ²_n`, the full
twist on the first `n` strands. Then
`C_{B_{n+1}}(Δ²_n) = B_n × ⟨Δ²_{n+1}⟩`.

**Consequences.**
- The set of `n` with `B_n` CAT(0) is an initial segment of the positive
  integers. It contains `1, …, 6` (`braid-groups-on-at-most-six-strands-are-cat0`),
  and `7` by Jeong (arXiv:2009.09350; not imported).
- Every braid group is CAT(0) iff infinitely many are. So
  `every-braid-group-is-cat0` reduces to
  `braid-groups-cat0-for-infinitely-many-strands`; see route
  `every-braid-group-cat0-from-infinitely-many-strands`.
- `some-braid-group-is-not-cat0` holds iff `B_n` fails to be CAT(0) for all
  large `n`. An obstruction at one `n_0` propagates to every `n ≥ n_0`. In
  particular, if `B_8` is not CAT(0), then no `B_n` with `n ≥ 8` is.
- If `B_n` is CAT(0), so are `B_n/⟨Δ²_n⟩` and `P_n/⟨Δ²_n⟩` (artifact,
  Corollary 5.4).

**What is new.** None of Haettel–Kielak–Schwer (arXiv:1304.5990v2), Jeong
(arXiv:2009.09350v1) or Bregman–Libgober–Zhu (arXiv:2411.18067v1) states this
implication; their full texts were searched on 2026-09-16. Those papers prove
CAT(0)-ness of the Brady–McCammond complex for each `n` in range, and HKS name
centralizer splitting only as a general consequence of CAT(0). The implication
here concerns arbitrary geometric actions, not a specific complex. The
ingredients are standard, so it may be folklore; no source was found.

**Limits.** This transfers CAT(0) structures downwards only. It constructs
nothing for `n ≥ 8`, and the space obtained for `B_n` is an abstract factor of a
Min-set, not the orthoscheme complex.
