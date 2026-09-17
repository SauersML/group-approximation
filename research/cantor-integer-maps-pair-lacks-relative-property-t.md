---
rg: 2
id: cantor-integer-maps-pair-lacks-relative-property-t
kind: claim
title: "The pair (C(C,Z) ⋊ V, C(C,Z)) does not have relative property (T); rigid subsets of C(C,Z) have bounded depth"
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
distinct_from:
  cantor-integer-maps-by-v-are-not-a-t-menable: that claim denies the Haagerup property of C(C,Z) ⋊ V and names relative (T) of this pair as a sufficient input; this claim proves that input false, so that route needs a different rigid subset
  lamp-cartan-inclusion-is-not-rigid: that uses i.i.d. measures on a dual where the acting group permutes coordinates exactly; here V only near-acts on cones (finitely many breaks per element) and the random character is an infinite product of transported non-atomic characters
  infinite-permutation-augmentation-pair-fails-relative-t: that treats permutation lamp pairs; C(C,Z) is not a permutation module over V
---

Let `C = {0,1}^N`, `A = C(C,Z)` (locally constant integer functions), and
`G = A ⋊ V` with `(h·k)(x) = k(h^{-1}x)`. By
`cantor-maps-by-v-embed-in-next-brin-thompson-group`, `G ≤ 2V`.

**Theorem.** The pair `(G, A)` does not have relative property (T). More
precisely, for every `p ∈ (0,1/2]` there is a unitary representation `π_p` of `G`
with no nonzero `A`-invariant vector and a unit vector `ξ_p` with
`‖π_p(g)ξ_p − ξ_p‖ → 0` as `p → 0`, for every `g ∈ G`.

**Stronger form (rigid subsets).** Let `A_d` be the functions constant on all
cones of depth `d`. If `Y ⊆ A` and `(G, Y)` has relative property (T) in
Cornulier's sense, then `Y ⊆ A_d` for some `d`. Also `(G, A_d)` is relatively
rigid for one `d ≥ 1` iff for all `d`, iff `(G, Z·1_{[0]})` is. So the
"rigid subgroup inside `C(C,Z)`" route to
`brin-thompson-2v-is-not-a-t-menable` reduces exactly to the question whether
`(C(C,Z) ⋊ V, Z·1_{[0]})` has relative property (T). That holds iff the
centre `Z·1_C` of `C(C,Z) ⋊ V` is relatively rigid (proof §7: push spectral
measures along `χ ↦ χ∘T`, where `T` transports functions into the cone `[0]`).
The centre has `scl(1_C) = 0`, so the class of the central extension is nonzero over `R` but has no bounded representative, and
no quasimorphism sees it.

**Construction.** Fix `ξ ∈ Â` with `ξ(1_C) = 1`. For a word `w` let
`ξ_w(k) = ξ(k∘ι_w)`, `ι_w(u) = wu`. Let `S` be the random set of words
containing each word independently with probability `p`, and
`χ_S = ∏_{w∈S} ξ_w`. For `k ∈ A_d`, factors with `|w| ≥ d` are `1`, so
`χ_S ∈ Â`. For `h ∈ V` and `w` not an internal node of the domain tree,
`h·ξ_w = ξ_{h(w)}`. A coupling gives `‖h_*ν_p − ν_p‖ ≤ 4p(n_h − 1)`, where
`ν_p` is the law of `χ_S` and `n_h` is the number of leaves. The Koopman–GNS
representation `π_p` on `L²(Σ_h c_h h_*ν_p)` has a unit vector `f_p` with
`π_p(g)f_p → f_p` for every `g ∈ G`. The exact formula
`E χ_S(k) = ∏_w (1 − p + p ξ(k∘ι_w))` gives
`|E χ_S(k)| ≤ exp(−p(1−p) E_ξ(k))` with
`E_ξ(k) = Σ_w (1 − Re ξ(k∘ι_w))`. Two facts finish the proof. First,
`ν_p({1}) = 0` for `ξ ≠ 1`, which gives no `A`-invariant vectors. Second, a
Baire argument on `Â` gives, for any `Y` of unbounded depth, a `ξ` with
`sup_Y E_ξ = ∞`. Then some `y ∈ Y` moves `f_p` by `> 0.88` for every `p`. The
full proof is in `cantor-integer-maps-pair-lacks-relative-property-t-proof`.

**What this kills and what it leaves.**

- Killed: the "concrete sufficient input" of
  `brin-thompson-2v-not-a-t-menable-via-cantor-integer-maps`, i.e. relative (T)
  of `(G, A)`. Also killed: relative (T) of `(G, Y)` for every `Y ⊆ A` of
  unbounded depth, e.g. `{1_{[0^d]}}` and the checkerboards
  `{Σ_{|w|=d} 1_{[w0]}}`.
- Left, and sharpened: relative (T) of `(G, Z·1_{[0]})`, equivalently of
  `(G, A_d)`, equivalently of the centre `(G, Z·1_C)`. Cone-product characters cannot decide it, because
  `χ_S(1_{[0]})` depends only on whether `∅ ∈ S`. Also left: rigid subsets of
  `G` not contained in `A`, and relative (T) of `(2V, Y)`.
- Not implied: the Haagerup property of `G`.
