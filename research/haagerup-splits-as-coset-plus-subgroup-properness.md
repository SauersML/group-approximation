---
rg: 2
id: haagerup-splits-as-coset-plus-subgroup-properness
kind: claim
title: "For any subgroup H of a countable group G: G has the Haagerup property iff some cnd function is proper modulo H and some cnd function on G is proper on H"
distinct_from:
  cantor-integer-maps-by-v-have-haagerup-property: that records the normal-subgroup case for C(C,Z) ⋊ V (a cnd function proper on the kernel plus Farley's function on the quotient); this is the general statement for an arbitrary, possibly non-normal, subgroup, which is what a simple group such as nV needs
---

**ESTABLISHED** by `haagerup-splits-as-coset-plus-subgroup-properness-proof`.

**Definitions.** `G` is a countable group and `H ≤ G`. A function `φ: G → [0, ∞)` is
*proper modulo `H`* if for every `R` the sublevel set `{g : φ(g) ≤ R}` is contained in a
finite union of left cosets `g_1 H ∪ ... ∪ g_r H`. It is *proper on `H`* if
`{h ∈ H : φ(h) ≤ R}` is finite for every `R`. A cnd function is a conditionally negative
definite function `ψ` with `ψ(e) = 0`, equivalently `ψ(g) = ‖b(g)‖²` for a 1-cocycle `b` of
an orthogonal representation.

**Statement.** The following are equivalent.

1. `G` has the Haagerup property (a proper cnd function exists).
2. There are cnd functions `ψ_1, ψ_2` on `G` such that `ψ_1` is proper modulo `H` and
   `ψ_2` is proper on `H`.

Moreover in (2) the sum `ψ_1 + ψ_2` is a proper cnd function.

**Use.** For a simple group such as `nV` there is no normal subgroup to split along. This
lemma splits the Haagerup property along any subgroup into two prerequisites that can fail
independently: a *transversal* one (properness on the coset space) and a *fibre* one
(properness on `H`, by a function defined on all of `G`). It is the bridge of the route
`brin-thompson-nv-a-t-menable-via-triangular-split`.
