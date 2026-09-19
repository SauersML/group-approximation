---
rg: 2
id: amenable-recursive-groups-have-recursive-expander-profile-proof
kind: route
title: Split a Følner set along cosets of a finite expander, then apply Cavaleri
target: amenable-recursive-groups-have-recursive-expander-profile
requires:
  - recursive-amenable-classes-have-uniform-folner-bounds
---

**Recursive presentability of subgroups.** If `H = <X> <= G` and `G` has
solvable word problem, then the set of words in `X` that are trivial in `H` is
decidable, so `H` is recursively presented.

**Item 1.**
1. **Setup.** Let `Γ <= H` be finite, and let `T ⊂ B_X(L)` be symmetric with
   `|T| <= L`, `<T> = Γ` and `h(Γ,T) >= δ`. Put `n = ⌈2L^2/δ⌉`, and let `Ω` be an
   `n`-Følner set of `H`, so `|Ω \ xΩ| <= |Ω|/n` for `x in X`.
2. **Short elements move `Ω` little.** For `y = x_1 ... x_l` with `l <= L` and
   `x_i in X ∪ X^-1`,
   `|Ω \ yΩ| <= Σ_i |Ω \ x_iΩ| <= L|Ω|/n`. For `x^-1` use
   `|Ω \ x^-1Ω| = |xΩ \ Ω| = |Ω \ xΩ|`, and for a product use
   `Ω \ abΩ ⊂ (Ω \ aΩ) ∪ a(Ω \ bΩ)`. Summing over `T`,
   `Σ_(y in T) |Ω \ yΩ| <= L^2 |Ω| / n <= (δ/2) |Ω|`.
3. **Split along right cosets.** Put `Ω_c = Ω ∩ Γc`. Since `y in Γ`,
   `yΩ ∩ Γc = yΩ_c`, so `Σ_c Σ_y |Ω_c \ yΩ_c| <= (δ/2) Σ_c |Ω_c|`. Some `c` with
   `Ω_c` nonempty has `Σ_y |Ω_c \ yΩ_c| <= (δ/2) |Ω_c|`.
4. **Cheeger.** Put `A = Ω_c c^-1 ⊂ Γ`. Right translation commutes with left
   multiplication, so `Σ_y |A \ yA| <= (δ/2)|A| < δ|A|`. As `h(Γ,T) >= δ`, this
   forces `|A| > |Γ|/2`, so `|Ω| >= |A| > |Γ|/2`.
5. Taking the least `Ω` and the largest admissible `Γ` gives item 1. The trivial
   `Γ` gives `F >= 1 > 1/2`.

**Item 2.** By `recursive-amenable-classes-have-uniform-folner-bounds`
(Theorem 3.1, (i) ⇒ (ii)), `F_(H,X) <= V` for a recursive `V`. Hence
`X^δ_(H,X)(L) < 2 V(⌈2L^2/δ⌉)`, which is recursive in `L`. ∎
