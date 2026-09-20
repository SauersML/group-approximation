---
rg: 2
id: triangle-edge-matching-reduces-to-one-edge-holonomy
kind: claim
title: For triangles of finite groups with cyclic edge groups and split vertex abelianizations, edge matching reduces to absorbing a mismatch on one edge
distinct_from:
  triangle-of-finite-groups-hs-stability-is-edge-matching: that proves flexible HS stability of the colimit is equivalent to (EM), where all three edges may disagree; this shows that under a split-abelianization hypothesis two of the three mismatches can always be removed exactly, so (EM) is equivalent to a statement where only one edge disagrees
  gowers-hatami-finite-group-hs-stability: that rounds approximate representations of one finite group; this aligns genuine representations of cyclic edge groups whose eigenvalue counts have been equalized by padding with linear characters
---

**ESTABLISHED.**

**Setting.** A triangle of finite groups:
- vertex groups `X_0, X_1, X_2`;
- edge groups cyclic of prime order `p`: `⟨b⟩ ⊂ X_0 ∩ X_1`, `⟨a⟩ ⊂ X_0 ∩ X_2`, `⟨c⟩ ⊂ X_1 ∩ X_2`
  (as in `triangle-of-finite-groups-hs-stability-is-edge-matching`, with the edge injections
  written as inclusions);
- `G` is the colimit.

**Hypothesis (SPLIT).** For each vertex group and its two edge generators, e.g. `X_0` with `a, b`,
the abelianization `X_0^ab` is `(Z/p)^2` with the images of `a` and `b` as a basis. So for every
pair `(j,k)` there is a linear character `χ` of `X_0` with `χ(a) = ζ^j`, `χ(b) = ζ^k`,
`ζ = e^(2πi/p)`. Likewise for `X_1` with `c, b` and `X_2` with `c, a`.

**(EM)** is as in `triangle-of-finite-groups-hs-stability-is-edge-matching`.

**(HA), one-edge holonomy absorption.** For all `d_n` and genuine representations
`ρ_{i,n} : X_i → U(d_n)` with

```text
ρ_{0,n}(b) = ρ_{1,n}(b),   ρ_{0,n}(a) = ρ_{2,n}(a)   exactly,   ||ρ_{1,n}(c) − ρ_{2,n}(c)||_2 → 0,
```

there are genuine `π_n : G → U(D_n)`, `D_n ≥ d_n`, `D_n/d_n → 1`, with
`||ρ_{i,n}(x) − P_n π_n(x) P_n*||_2 → 0` for every `i` and every `x ∈ X_i`.

**Theorem.** Under (SPLIT), (EM) holds if and only if (HA) holds. Hence `G` is flexibly HS stable if
and only if (HA) holds.

**What it isolates.** Two of the three edge disagreements can always be removed exactly, at the cost
of `O(ε² d)` padding by linear characters and a conjugation within `O(ε)` of the identity. What
remains is the holonomy around the triangle: after `b` and `a` agree exactly, the mismatch on `c`
must be absorbable, up to `o(d)` padding.

**Quantitative lemmas.** Write `s_p = 2 sin(π/p)`. The independently reviewed
`hrf-cyclic-edge-quadratic-padding` proof gives:
- **(L1) Padding.** If all edge errors are at most `ε`, linear-character sums of
  common dimension `m ≤ p ε² d/s_p²` equalize all three spectral multiplicity vectors.
- **(L2) Alignment.** Equal-multiplicity order-`p` unitaries at normalized HS
  distance `η` admit an intertwiner `w` with `||w − I||₂ ≤ 2η/s_p`.
- After padding, each error is at most `η ≤ sqrt(1+4p/s_p²) ε`; aligning two
  edges leaves the third error at most `(1+8/s_p)η`.

These estimates improve preprocessing only; the (HA) assertion is still a
separate simultaneous rounding problem.

**Credit.** Elementary. No priority is claimed.

DERIVATION
triangle-edge-matching-one-edge-holonomy-proof
