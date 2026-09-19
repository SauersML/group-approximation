---
rg: 2
id: fpbs-mal-two-step-relative-position-rigidity
kind: claim
title: Two classes of K = <a, bab^-2> in F(a,b) have at most 12 common neighbours at any prescribed pair of relative positions
distinct_from:
  fpbs-malnormal-subgroup-relations-finite-contacts: that bounds edges between two fixed classes (one step); this bounds two-step detours between two fixed classes, uniformly in both double cosets.
  fpbs-mal-stage-block-sprinkling-threshold: that counts simple paths of the single label b in the hull nerve, with bounds exponential in path length; this handles arbitrary pairs of labels of any length, with an absolute bound for length two.
  fpbs-mal-simple-chain-count-uniform: that is the open all-length version; this is its length-two case with arbitrary endpoints.
artifacts:
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/overlap.py
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/two_step.py
  - experiments/fpbs-iid-chord-union-bound-2026-09-17/two_step_out.txt
---

**ESTABLISHED** through `fpbs-mal-two-step-relative-position-rigidity-proof`.

Let `F = F(a, b)` and `K = <a, b a b^{-2}>`. For right cosets `A = Ky` and
`B = Kz`, the *relative position* is the double coset
`D(A, B) = K z y^{-1} K`. A chord `(y, h y)` joins classes at relative
position `KhK`.

**Claim.** For all right cosets `A ≠ B` of `K` and all double cosets
`D, D' ≠ K`,

```text
#{ C ∉ {A, B} : D(A, C) = D  and  D(C, B) = D' }  <=  12 .
```

The bound does not depend on the word lengths of `D`, `D'`, nor on the
relative position of `A` and `B`.

**Meaning.** Two chords of any lengths can close a detour between two given
`K`-classes in at most 12 ways. Unions of independent chords are controlled
by counts of vertex-simple chains of relative positions, and this is the
length-two case of that count (see `fpbs-mal-simple-chain-count-uniform`).

**Data.** The count takes values in `{0, 1, 2}` for 21 target classes and all
labels of length at most 3 (`two_step_out.txt`).
