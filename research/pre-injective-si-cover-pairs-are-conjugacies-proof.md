---
rg: 2
id: pre-injective-si-cover-pairs-are-conjugacies-proof
kind: route
title: Unique lifts define a local transport cocycle, transport to a constant image splits the cover as a product over the fibre, and strong irreducibility collapses a fibre with no asymptotic pairs to one constant
target: pre-injective-si-cover-pairs-are-conjugacies
requires:
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
  - injective-automaton-images-are-sft-cover-pairs
artifacts:
  - research/artifacts/pre-injective-cover-pair-products-2026-09-20.md
---

Conventions are those of the claim. `Δ(x, x')` is the set of sites where `x` and `x'` differ, and `x ~ x'` means
that it is finite. `F` has memory `M`, and `X` has a finite defining window. Put `N = Φ^-1`. The single-site case of
the lift property reads as follows: if `z` differs from `F(x)` only at `h`, there is a lift `x'` with
`Δ(x, x') ⊆ hΦ`.

The two prerequisites are used only in the corollary. The first gives `PSD ⇒ Gottschalk`, and the second makes
`τ(A^G)` a proper SI SFT cover pair when `τ` is injective and not surjective. Steps 1 to 7 use only the definitions.

**Step 1 (unique lifts).** Let `x ∈ X` and `y ~ F(x)`. A lift exists: lift the sites of `Δ(F(x), y)` one at a
time. By pre-injectivity it is unique. Call it `L(x, y)`. It is equivariant: `L(gx, gy) = g L(x, y)`, because
`gL(x, y)` is a lift of `gy` asymptotic to `gx`. Every sequence of single-site lifts that ends at image `y`
ends at `L(x, y)`, whatever the order.

**Step 2 (single-site lifts are local).** Let `z` differ from `F(x)` only at `h`. The unique lift `x'` agrees
with `x` off `hΦ`. Let `V_h = hΦ ∪ hΦ M^-1 M ∪ hΦ K`, where `K` is `W^-1 W` for a defining window `W` of `X`.
A pattern `p` on `hΦ` is *admissible* if the configuration `x[p]`, which is `x` with `p` written on `hΦ`, has no
forbidden window meeting `hΦ` and satisfies `F(x[p]) = z` on `hΦ M^-1`. Admissibility depends only on `x|V_h`
and `z(h)`.
- Since `X` is an SFT, and `x` has no forbidden window, `x[p] ∈ X` for admissible `p`.
- `F(x[p])` and `F(x)` can differ only on `hΦM^-1`. So `F(x[p]) = z` everywhere.
- So every admissible `p` gives a lift. By uniqueness there is exactly one admissible `p`, namely `x'|hΦ`.
- Hence `x'|hΦ = λ_h(x|V_h, z(h))` for a function `λ_h`. By equivariance `λ_h` is a translate of `λ_1`.

**Step 3 (the transport).** For `x ∈ X` and any `y ∈ A^G`, let `y_N` equal `y` on `N` and `F(x)` off `N`. Then
`y_N ~ F(x)`. Define `S(x, y)(1) = L(x, y_N)(1)` and `S(x, y)(g) = S(g^-1 x, g^-1 y)(1)`.
- Compute `L(x, y_N)` by single-site lifts at the sites of `N`, in a fixed order.
- Each such lift writes only on `hΦ` and reads only `V_h` and `y(h)`. So the result on `E = ∪_{h ∈ N} V_h`
  depends only on `x|E` and `y|N`.
- So `S` is given by a local rule with windows `E` for `x` and `N` for `y`. It is continuous and equivariant.

**Step 4 (agreement on asymptotic data).** Let `y ~ F(x)`. Reach `L(x, y)` in two stages. First lift at the sites
of `N`, which gives `L(x, y_N)`. Then lift at the remaining sites `h` of `Δ(F(x), y) \ N`. Each later lift writes
only on `hΦ`, and `1 ∉ hΦ` because `h ∉ Φ^-1`. By Step 1 the result is `L(x, y)`, so
`L(x, y)(1) = L(x, y_N)(1) = S(x, y)(1)`. Equivariance of `L` gives `L(x, y) = S(x, y)` at every site.

**Step 5 (identities).** Fix `x` and `y`. Let `y_n` equal `y` on the ball `B_n` and `F(x)` off it. Then
`y_n ~ F(x)`, so `S(x, y_n) = L(x, y_n)` lies in `X` and has image `y_n`. By locality, `S(x, y_n)` agrees with
`S(x, y)` at every `g` with `gN ⊆ B_n`, so `S(x, y_n) → S(x, y)`. Since `X` is closed and `F` is continuous,
`S(x, y) ∈ X` and `F(S(x, y)) = y`. Also `S(x, F(x)) = L(x, F(x)) = x`.
- *Cocycle.* For `y, z ~ F(x)`, both `S(S(x, y), z)` and `S(x, z)` are asymptotic to `x` and have image `z`. By
  uniqueness they are equal. Such pairs `(y, z)` are dense in `A^G × A^G`. Both sides are continuous in `(y, z)`,
  because `S` is jointly continuous. So `S(S(x, y), z) = S(x, z)` for all `x, y, z`.

**Step 6 (product splitting).** Put `Π(x) = (S(x, d^G), F(x))` and `Σ(z, y) = S(z, y)` for `z ∈ Z = F^-1(d^G)`.
- `Π` lands in `Z × A^G`, since `F(S(x, d^G)) = d^G`.
- `Σ(Π(x)) = S(S(x, d^G), F(x)) = S(x, F(x)) = x`.
- `Π(Σ(z, y)) = (S(S(z, y), d^G), y) = (S(z, d^G), y) = (S(z, F(z)), y) = (z, y)`.

Both maps are automata, so `Π` is a conjugacy with `pr_2 ∘ Π = F`.
- `Z` is nonempty: pick `x ∈ X`; then `S(x, d^G) ∈ Z`.
- `Z = X ∩ F^-1(d^G)` is an SFT, because `X` is one and `F` is local.
- No two distinct points of `Z` are asymptotic: they would be distinct asymptotic points of `X` with the same
  image `d^G`.
- `Z` is the image of `X` under the automaton `r(x) = S(x, d^G)`, which is a retraction onto `Z`.

This proves Theorem S.

**Step 7 (strong irreducibility collapses the fibre).** Assume `X` is SI.
- *`Z` is SI.* Let `r` have memory `R`, and let `Δ_X` be an SI constant for `X`. Put `Δ_Z = R Δ_X R^-1`. Let
  `Ω_1 Δ_Z ∩ Ω_2 = ∅` and `z_1, z_2 ∈ Z`. Then `(Ω_1 R) Δ_X ∩ Ω_2 R = ∅`. So some `x ∈ X` agrees with `z_1` on
  `Ω_1 R` and with `z_2` on `Ω_2 R`. Since `r(z_i) = z_i`, the point `r(x) ∈ Z` agrees with `z_1` on `Ω_1` and
  with `z_2` on `Ω_2`.
- *Splicing in `Z`.* Let `W ∋ 1` be a window such that `Z` is defined by forbidden patterns on translates of
  `W`. Let `z, z' ∈ Z` and `k ∈ G`. Put `K = {k} Δ_Z` and `B = K W^-1 W`. By SI there is `w ∈ Z` with `w(k) = z'(k)`
  and `w = z` on the finite set `B \ K`. Let `v` equal `w` on `B` and `z` off `B`.
  - A window `gW` that meets `K` has `g ∈ K W^-1`, so `gW ⊆ B`, where `v = w`.
  - A window that misses `K` sees `v = z` throughout, since `w = z` on `B \ K`.
  - So `v ∈ Z`, `v ~ z` and `v(k) = z'(k)`.
- *Collapse.* If `z(k) ≠ z'(k)`, then `v ≠ z` are distinct asymptotic points of `Z`, which Step 6 excludes. So
  all points of `Z` agree everywhere, and `Z = {z_0}` because `Z` is nonempty. `Z` is invariant, so `z_0` is fixed by
  `G`, i.e. `z_0 = c^G` for some `c ∈ A`.
- *Conjugacy.* `Π(x) = (c^G, F(x))`, so `F = pr_2 ∘ Π` is a conjugacy `X → A^G`. If `X ≠ A^G`, then `F^-1` is an
  automaton `A^G → A^G` that is injective, with image `X` proper. This proves Theorem C.

**Step 8 (corollaries).**
1. *Gottschalk.* If `G` is surjunctive, Theorem C shows that no proper SI SFT cover pair is pre-injective.
   Conversely, let `τ : A^G → A^G` be injective and not surjective. By `injective-automaton-images-are-sft-cover-pairs`,
   `(τ(A^G), τ^-1)` is a proper SI SFT cover pair, and it is bijective, hence pre-injective.
2. *PSD.* `NoCover_SI(G) ⇒ PSD(G)` holds vacuously. Conversely assume `PSD(G)`, and let `(X, F)` be a proper SI SFT
   cover pair. By PSD it is pre-injective. By `strict-pairs-give-dual-failures-on-bounded-defect-domains`, `G` is
   surjunctive. That contradicts Corollary 1. So there is no such pair.
3. *Split.* Corollaries 1 and 2 give `PSD(G) ⟺ Gottschalk(G) ∧ PSD_col(G)`, where `PSD_col(G)` means that no
   proper SI SFT cover pair collides. Both sides equal `NoCover_SI(G)`.
