---
rg: 2
id: bg-in-isometric-brick-hosts-needs-unbounded-exponents
kind: claim
title: In any group of brick maps of C^n with isometric sections (nV, 2V_tau, the affine 2V hosts), a nontrivial image of the Baumslag--Gersten generator a has zero periodic exponents, unbounded exponent sums and zero entropy, so the landed BS(1,2) copies in 2V_tau never extend to BG
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that treats nV with trivial sections and any proper-power relation; this allows isometric sections (odometer and affine 2-adic unit sections), and uses the stable letter of BG to force unbounded exponent sums.
  baumslag-gersten-equicontinuous-generator-acts-trivially: that is the dynamical input (equicontinuous a acts trivially); this identifies, for brick hosts with isometric sections, bounded exponent sums as the exact condition that makes a equicontinuous.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that proves bounded sums from a proper-power relation in one dimension by pumping; in dimension n >= 2 pumping fails, and this claim does not replace it -- it records that BG forces the unbounded case.
  odometer-2v-is-fp-simple-and-contains-bs12: that puts BS(1,2) = <s,u> in 2V_tau; this shows that copy is not the <a,b> of any image of BG.
---

**ESTABLISHED** (lane proof, elementary; no novelty claimed). Reviewed: gq-referee-a PASS,
proof-gap lens (`research/artifacts/gq-referee-a-bg-in-isometric-brick-hosts-needs-unbounded-exponents.md`,
5d3e18e0b; nits N1 and N2 applied below), and gq-referee-b PASS, citation lens
(`research/artifacts/gq-referee-b-bg-in-isometric-brick-hosts-needs-unbounded-exponents.md`,
a8dffeea3; W1 applied: the entropy bound is now proved directly by spanning sets).

## Setting

- `C = {0,1}^N`, `C(u)` the cone of words beginning with `u`, and a *brick* is
  `Π_j C(u_j) ⊆ C^n`. On `C^n` use `d(x,y) = 2^(-m(x,y))`, where `m(x,y)` is the least
  over `j` of the common-prefix length of `x_j, y_j`.
- An *isometric-section brick map* is a homeomorphism `g` of `C^n` with a *table*: two
  partitions of `C^n` into bricks `Π_j C(u_{ij})` and `Π_j C(v_{ij})` and isometries
  `h_{ij}` of `(C, d)` (automorphisms of the binary rooted tree) with
  `g(u_{i1}w_1, …, u_{in}w_n) = (v_{i1}h_{i1}(w_1), …, v_{in}h_{in}(w_n))`.
  `L(g)` is the least maximal word length over tables. These maps form a group `𝔅_n`.
- Examples: Brin's `nV` (all `h = id`); `2V_τ` of `odometer-2v-is-fp-simple-and-contains-bs12`
  (`h = τ^k` on coordinate 1, `id` on coordinate 2); the affine hosts `2V_{G_N}` of
  `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q` (sections `x ↦ p^k x + c` on `Z_2`
  with `p^k` a 2-adic unit, which are isometries); for `n = 1`, Röver--Nekrashevych groups.
- `δ_g(x) = (|v_{ij}| − |u_{ij}|)_j ∈ Z^n` on the table brick containing `x`, and
  `S_m(x) = δ_{g^m}(x)`.

## Statement

Let `BG = ⟨a, t | b a b^{-1} = a^2⟩`, `b = t a t^{-1}`, and let `φ: BG → 𝔅_n` be a
homomorphism with `g = φ(a) ≠ id`. Then:
1. **Zero periodic exponents.** `δ_{g^p}(x) = 0` for every `g`-periodic `x` of least period `p`.
2. **Unbounded exponent sums.** `sup_{m ∈ Z, x ∈ C^n} |S_m(x)|_∞ = ∞`.
3. **Zero entropy.** `h(g) = h(φ(b)) = 0`, and every element of `𝔅_n` has finite entropy
   `h(f) ≤ n L(f) log 2`.

**Consequences.**
- In `2V_τ`, `s = τ × id` has `δ_s ≡ 0`, so by item 2 no homomorphism `BG → 2V_τ` sends `a`
  to `s`. The inverse baker map `u` has `h(u) ≥ log 2` (item 4 of
  `brin-thompson-proper-power-conjugates-have-zero-entropy`), so by item 3 no homomorphism
  sends `b` to `u`. So the landed `BS(1,2) = ⟨s, u⟩` is never the `⟨a, b⟩` of an image of
  `BG`. The same argument excludes, in any of these hosts, every `BS(1,2)` copy whose base
  element has bounded exponent sums (for example a pure-section element with `δ ≡ 0`), or
  whose conjugator has positive entropy.
- A `BG` image in any of these hosts lives in the same regime as a witness for
  `bs12-embeds-in-brin-thompson-2v`: zero periodic spectrum together with unbounded
  exponent sums. It needs in addition that the conjugator `b` has zero entropy.

**Sharpness.** Item 2 needs the stable letter `t`: `BS(1,2) = ⟨s, u⟩ ≤ 2V_τ` has
`u s u^{-1} = s^2` with bounded sums for `s`. Item 1 needs only `b a b^{-1} = a^2`.

## Proof

**Item 1.** This is Step 1 of `brin-thompson-exponent-cocycle-proof` with `f = φ(b)`, `k = 1`,
`l = 2`. The steps use only that `δ` is a well-defined, locally constant cocycle bounded by
`L(g)`. That holds here: splitting coordinate `j` of a table brick by one digit `c` replaces
`C(u_j) → C(v_j)` by `C(u_j c) → C(v_j h(c))`, with the same length difference and section
`h|_c`, again an isometry; and composing tables appends digits to domain and range words
together, so length differences add.

**Item 2.** Suppose `|S_m(x)|_∞ ≤ K` for all `m ∈ Z` and `x`. Put `L = L(g) = L(g^{-1})`.
- *Reading lengths.* For `m ≥ 0` and each coordinate `j`, let `ℓ^j_m(x)` be the least length
  such that `g^m` acts on the brick of `x` with those prefix lengths as a brick map
  `(u_j w_j) ↦ (v_j η_j(w_j))`, `η_j` isometries. If `g^m` sends such a brick onto
  `Π C(p_j)` with `|p_j| = |u_j| + S^j_m(x) < L`, extend `u_j` by the next `L − |p_j|` digits
  of `x_j`. An isometry maps a cone of the extra length onto a cone of the same length, so
  the image brick then has every prefix length `≥ L`. A brick all of whose prefixes `p_j`
  have length `≥ L` lies in one table brick of `g`, because the table prefixes (of length
  `≤ L`) containing a point of it are prefixes of the `p_j`. Hence
  `ℓ^j_{m+1}(x) ≤ max(ℓ^j_m(x), L − S^j_m(x))`. Starting from `ℓ^j_0 = 0`, induction gives
  `ℓ^j_m(x) ≤ L + K` for all `m ≥ 0`.
  The same holds for `g^{-1}`, since `S_m(g^{-1}, x) = −S_m(g, g^{-m} x)`.
- *Equicontinuity.* Put `N = L + K`. Every `g^m`, `m ∈ Z`, acts on every level-`N` brick as
  `(u_j w_j) ↦ (v_j η_j(w_j))` with `|v_j| ≥ N − K`. If `x, y` lie in one level-`N` brick with
  common prefix lengths `c_j ≥ N`, then `g^m x, g^m y` have common prefix lengths
  `c_j + S^j_m ≥ c_j − K`. So `d(g^m x, g^m y) ≤ 2^K d(x, y)` whenever `d(x, y) < 2^{-N}`,
  and `{g^m}` is equicontinuous.
- *Contradiction.* `C^n` is compact, zero-dimensional and metrizable, and `BG` acts on it
  through `φ`. By `baumslag-gersten-equicontinuous-generator-acts-trivially`, `a` acts
  trivially, so `g = id`. That contradicts the hypothesis.

**Item 3.** If `d(x, y) < 2^{-L(f)+1}`, then `x, y` lie in one table brick `Π C(u_j) → Π C(v_j)`
of `f`, and their common prefix lengths change by `|v_j| − |u_j| ≥ −|u_j| ≥ −L(f)`. Otherwise
`d(x,y) ≥ 2^{-L(f)+1}`, and `d(fx, fy) ≤ diam(C^n) = 1 ≤ 2^{L(f)-1} d(x,y)`. So `f` is
`2^{L(f)}`-Lipschitz, so `d(f^i x, f^i y) ≤ 2^{iL(f)} d(x,y)`.

*Spanning sets* (Bowen's definition: `E` is `(k,ε)`-spanning if every `x` has `y ∈ E` with
`d(f^i x, f^i y) ≤ ε` for `0 ≤ i < k`). Given `ε > 0` and `k ≥ 1`, put
`m = ⌈log_2(1/ε)⌉ + (k−1)L(f)` and pick one point in each brick `Π_j C(u_j)` with all
`|u_j| = m`. Every `x` shares such a brick with a chosen `y`, so `d(x,y) ≤ 2^{-m}` and
`d(f^i x, f^i y) ≤ 2^{(k-1)L(f) - m} ≤ ε` for `i < k`. This spanning set has `2^{nm}`
points, so `(1/k) log r_k(ε) ≤ (n/k)(⌈log_2(1/ε)⌉ + (k−1)L(f)) log 2`, which tends to
`n L(f) log 2` as `k → ∞`. Hence `h(f) ≤ n L(f) log 2 < ∞`, with no box-dimension theorem.

Now `φ(b) g φ(b)^{-1} = g^2` gives `h(g) = h(g^2) = 2h(g)`, so `h(g) = 0`, and
`h(φ(b)) = h(g)` because `φ(b) = φ(t) g φ(t)^{-1}`. These use the textbook facts
`h(T^k) = |k| h(T)` and invariance of entropy under conjugacy (Walters, *An Introduction to
Ergodic Theory*, Ch. 7; not re-read). Items 1 and 2 do not use entropy.
