---
rg: 2
id: brin-thompson-2v-three-pass-fibre-products-miss-the-baker-map
kind: claim
title: "In 2V the three-pass product L_1 L_2 L_1 of the two coordinate fibre groups contains V×V and every grid permutation, but misses every nonzero power of the baker map: its elements transport a fibre-probability measure to a fibre-probability measure"
distinct_from:
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that makes elements of the fibre group K_2 = L_2 elliptic in commensurating actions; this is about which elements of 2V are short products of fibre-group elements, and is action-free
  brin-thompson-nv-haagerup-iff-proper-modulo-triangular: that reduces the Haagerup property to properness modulo T_2 = L_2 ⋊ V; this shows 2V is not the three-pass product L_1 L_2 L_1 of the fibre groups inside T_2 and its swap
  nv-gap-class-cocycles-are-coboundaries: that remarks that no bounded generation is needed for the gap class; this records the precise obstruction to the most natural bounded generation (Clos three-pass)
  brick-groupoid-has-zn-cocycle-with-af-kernel: that defines the Z^n exponent cocycle; this uses its y-component as the obstruction and shows its kernel's grid part lies in L_1 L_2 L_1
---

**ESTABLISHED** by `brin-thompson-2v-three-pass-baker-obstruction-proof`
(self-contained; uses only P. Hall's marriage theorem).

**Setting.** `C = {0,1}^ω` with Lebesgue (coin-flip) measure `λ`. `2V` acts on `C × C` by
brick maps. The two coordinate fibre groups are

```text
L_1 = { (x,y) ↦ (F(y)(x), y) : F : C → V locally constant } ,
L_2 = { (x,y) ↦ (x, G(x)(y)) : G : C → V locally constant } ,
```

each isomorphic to `C(C,V)`, with `L_1 = α L_2 α` for the coordinate swap `α` (an
automorphism of `2V`, not an element). `L_2` is the fibre group `K_2` inside the triangular
subgroup `T_2 = L_2 ⋊ (V × 1)`. For `h ∈ 2V` and `p ∈ C²` let `c_y(h,p) ∈ Z` be the base-2
logarithm of the `y`-derivative of `h` at `p` (the `y`-component of the exponent cocycle; on a
brick `[a]×[b] → [c]×[d]` it equals `|b| − |d|`), and `c_x` likewise. The baker map is
`β(x_1 x', y) = (x', x_1 y)`, with `c_x ≡ +1` and `c_y ≡ −1`.

**Theorem.**

1. *(Large.)* `L_1 L_2 L_1 ⊇ (V × V) ∪ K`, where `K` is the group of all grid permutations:
   maps permuting the cells `[a]×[b]` (`|a| = p`, `|b| = q`, for some `p, q`) by canonical
   translations. Hence it contains the grid part of the exponent-cocycle kernel.
2. *(Transport invariant.)* For every `g ∈ L_1 L_2 L_1` there is a probability measure `μ` on
   `C²` of full support, with `y`-marginal `λ`, such that `∫ 2^{c_y(g,p)} dμ(p) = 1`.
3. *(Obstruction.)* Consequently, if `c_y(g,·) ≤ 0` everywhere, or `≥ 0` everywhere, then
   `c_y(g,·) ≡ 0`. In particular `β^N ∉ L_1 L_2 L_1` for `N ≠ 0`. Swapping coordinates,
   `β^N ∉ L_2 L_1 L_2` either. So `2V ≠ L_1 L_2 L_1` and `2V ≠ L_2 L_1 L_2`.

**Why it is recorded.**

- A bounded generation `2V = (L_1 L_2)^k` would make "`2V` has (T)" equivalent to relative
  property (T) of `(2V, L_2)`. It would also make FW of `2V` equivalent to bounded `L_2`-orbits
  in commensurating actions. The reason: `√ψ` is subadditive, and `ψ∘α` is cnd whenever `ψ` is.
- The Clos/König three-pass argument proves exactly part 1. It is the natural attempt at `k`
  near 1. This claim shows that it cannot reach the baker map. The obstruction is the fibre
  transport `T_h μ = h_*(2^{c_y(h)} μ)`:
  - `L_1` preserves `y`-marginals;
  - `L_2` fixes `λ ⊗ λ`;
  - so a three-pass product maps some fibre-probability measure to another, which conserves
    mass.
- The baker map halves every fibre mass.
- **Left open:**
  - whether `2V = (L_1 L_2)^k` for some `k ≥ 2`. The transport invariant says nothing for four
    or more factors.
  - whether `⟨L_1 ∪ L_2⟩ = 2V`.
- **Relevance to the Haagerup goal.** Bounded generation gives only *upper* bounds on a cnd
  function. So it cannot supply the lower bounds that
  `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` needs. That hole is untouched.
