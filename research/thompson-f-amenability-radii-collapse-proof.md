---
rg: 2
id: thompson-f-amenability-radii-collapse-proof
kind: route
title: The one-Ramsey-call bound closes the degree-order chain, and two elementary Følner lemmas (connected components one way, lazy-walk smoothing plus layer cake the other) add the Følner function to the same class
target: thompson-f-amenability-radii-collapse-to-one-tower-degree
requires:
  - thompson-f-coarse-reiter-radius-is-one-ramsey-call-away
  - thompson-f-ramsey-radii-in-the-elementary-degree-order
  - coarse-ball-invariance-gives-fine-reiter-measures
  - thompson-f-folner-function-exceeds-every-tower
---

Notation is as in the claim. "Degree order (n)" means clause `n` of
`thompson-f-ramsey-radii-in-the-elementary-degree-order`, and "CRE(E)" means Corollary 1 of
`thompson-f-coarse-reiter-radius-is-one-ramsey-call-away`: `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N ≥ 1`.
Towers are `exp_0(x) = x` and `exp_{j+1}(x) = 2^{exp_j(x)}`. For a measure `ν`, `(gν)(x) = ν(g⁻¹x)`, and `‖·‖` is the
ℓ¹ norm. Every function below is nondecreasing: this holds for `R`, `ψ` and `ψ_l` by (P1) of the degree-order proof,
for `CR` because `B_M ⊆ B_{M+1}`, and for `Føl` because a `1/(k+1)`-Følner set is `1/k`-Følner.

## Clause 1 (SFC)

Degree order (3) gives `R(t) ≤ ψ(2t)` for all `t ≥ 1`. Put `t = exp_E(N) ≥ 1` in CRE(E). Then use monotonicity of
`ψ`, the bound `2t ≤ 2^t = exp_1(t)` for integers `t ≥ 1`, and `x ≤ 2^x`:

`CR(N) ≤ exp_E(R(exp_E N)) ≤ exp_E(ψ(2·exp_E N)) ≤ exp_E(ψ(exp_{E+1} N)) ≤ exp_{E+1}(ψ(exp_{E+1} N))`.

So `CR ≼ ψ`. That is SFC, and SFG (`CR ⋠ ψ`) is false. ∎

## Clause 2 (Følner, lower): `CR(M) ≤ Føl(2M) − 1`

If `Føl(2M) = ∞` there is nothing to prove. Put `k = 2M` and let `A` be a nonempty finite set with
`|sA △ A| ≤ |A|/k` for `s ∈ S` and `|A| = Føl(k)`.

1. **Boundary count.** For finite `X`, put `β(X) = Σ_{s∈S} |sX \ X|`. Since `|sX| = |X|`, we have
   `|sX △ X| = 2|sX \ X|`, so `β(A) ≤ |A|/k`.
2. **Components.** Let `Γ` be the graph on `F` with edges `x — sx` for `s ∈ S`. Split `A` into the connected
   components of the induced subgraph `Γ[A]`. Take a component `C` and `c ∈ C`. If `sc ∈ A`, then `sc ∈ C`, because
   `c — sc` is an edge inside `A`. Hence `sC \ C = { sc : c ∈ C, sc ∉ A }`, and
   `β(C) = Σ_s |{c ∈ C : sc ∉ A}|`. Summing over components gives `Σ_C β(C) = Σ_s |{a ∈ A : sa ∉ A}| = β(A)`.
   Since `Σ_C |C| = |A|`, some component has `β(C) ≤ |C|/k`.
3. **Invariance.** For that `C`, `|sC △ C| = 2|sC \ C| ≤ 2β(C) ≤ 2|C|/k`. Let `ν` be uniform on `C`. Then
   `‖sν − ν‖ = |sC △ C|/|C| ≤ 2/k`, and also `‖s⁻¹ν − ν‖ = ‖ν − sν‖ ≤ 2/k`. By the triangle inequality and
   left-invariance of `‖·‖`, `‖gν − ν‖ ≤ 2|g|/k ≤ 1` for every `g ∈ B_M`.
4. **Support.** Right multiplication `x ↦ xh` is an automorphism of `Γ` (it maps `x — sx` to `xh — sxh`), and it
   commutes with the left action. Put `C' = Cc⁻¹` for some `c ∈ C`, and let `ν'` be uniform on `C'`. Then `C'` is
   connected in `Γ`, contains `e`, and `‖gν' − ν'‖ = ‖gν − ν‖`. Every `x ∈ C'` is joined to `e` by a path in
   `Γ[C']` with at most `|C'| − 1` edges, so `x = s_n^{±1}⋯s_1^{±1}` with `n ≤ |C'| − 1`. Hence
   `C' ⊆ B_{|C|−1} ⊆ B_{|A|−1}`.

So `CR(M) ≤ |A| − 1 = Føl(2M) − 1`. ∎

## Clause 3 (Følner, upper): `Føl(k) ≤ 5^{CR(1110k²) + 555k² − 1}`

If `CR(1110k²) = ∞` there is nothing to prove. Put `K = 555k²` and `r = CR(2K)`, and take `ν ∈ P(B_r)` with
`‖gν − ν‖ ≤ 1` for all `g ∈ B_{2K}`.

1. **Smoothing.** Apply `coarse-ball-invariance-gives-fine-reiter-measures` with `|S'| = 5`. It gives `μ` supported
   in `B_{r+K−1}` with `‖sμ − μ‖ ≤ δ := 10√(2 ln 2 / K)` for `s ∈ S`. Now
   `δ² = 200 ln 2 / (555k²) < 0.2498/k²`, so `δ < 1/(2k)`.
2. **Layer cake (Namioka).** For `t > 0` put `A_t = {x : μ(x) > t}`, a finite subset of `B_{r+K−1}`. Then
   `{sμ > t} = sA_t`. For reals `a, b ≥ 0`, `|a − b| = ∫_0^∞ |1[a > t] − 1[b > t]| dt`. Summing over `x` gives
   `‖sμ − μ‖ = ∫_0^∞ |sA_t △ A_t| dt` and `1 = ‖μ‖ = ∫_0^∞ |A_t| dt`. Hence

   `∫_0^∞ ( Σ_{s∈S} |sA_t △ A_t| − 2δ|A_t| ) dt ≤ 2δ − 2δ = 0`.

   The integrand is a step function in `t` that vanishes where `A_t = ∅`. So some `t` with `A_t ≠ ∅` has
   `Σ_s |sA_t △ A_t| ≤ 2δ|A_t| < |A_t|/k`, and in particular `|sA_t △ A_t| ≤ |A_t|/k` for each `s ∈ S`.
3. **Size.** `|B_n| ≤ 1 + 4·(3^n − 1)/2 = 2·3^n − 1 ≤ 5^n` for `n ≥ 0`. So
   `Føl(k) ≤ |A_t| ≤ |B_{r+K−1}| ≤ 5^{CR(1110k²) + 555k² − 1}`.
4. **Tower form.** By (P3) of the degree-order proof, `CR(M) ≥ M/2`, so `r ≥ K ≥ 555`. The exponent is at most
   `2r`, and `5^{2r} = 25^r ≤ 2^{2^r} = exp_2(r)`, since `r·log₂25 < 4.65r ≤ 2^r` for `r ≥ 5`. Also
   `1110k² ≤ exp_4(k)` for `k ≥ 1`, since `exp_4(1) = 65536` and the right side grows faster. So
   `Føl(k) ≤ exp_2(CR(exp_4 k)) ≤ exp_4(CR(exp_4 k))`. ∎

## Clause 4 (collapse)

- `R ≼ ψ` and `ψ ≼ CR` hold by degree order (3), and `CR ≼ R` holds by CRE(E). So `R ≈ ψ ≈ CR`.
- `ψ_l ≈ CR` for `l ≥ 2` holds by degree order (2).
- `CR ≼ Føl` holds by clause 2: `CR(M) ≤ Føl(2M) ≤ Føl(exp_1 M) ≤ exp_1(Føl(exp_1 M))`.
- `Føl ≼ CR` holds by clause 3.

The relation `≼` is transitive, so every pair in `𝓡 = {R, ψ, ψ_l, CR, Føl}` is `≈`-equivalent. ∎

## Corollaries

- **Every gap is false.** `φ ⋠ χ` contradicts clause 4 for all `φ, χ ∈ 𝓡`. The named statements are:
  - SFG is `CR ⋠ ψ`;
  - ¬AMP is `ψ ⋠ R` by degree order (4);
  - RGAP₁ is `CR ⋠ R` by degree order (4);
  - RGAP₂ implies ¬AMP by the sandwich;
  - PGAP_1 implies RGAP₁ (the note in `ramsey-functions-are-pairwise-reiter-radii`).

  The last four were already refuted in `thompson-f-coarse-reiter-radius-is-one-ramsey-call-away`, Corollaries 2
  and 3. SFG is the new one: CRE alone refutes RGAP₁, and degree order (5) splits RGAP₁ into `¬AMP ∨ SFG`. The
  failure of RGAP₁ kills both disjuncts, so it kills SFG. Clause 1 records this directly.
- **Nothing in `𝓡` is elementary.**
  - Suppose `F` is amenable. `thompson-f-folner-function-exceeds-every-tower` gives, for every `p`, some `k` with
    `Føl(k) > exp_p(k)`. Suppose `φ ∈ 𝓡` had `φ ≤ exp_q` everywhere. Then
    `Føl(x) ≤ exp_E(φ(exp_E x)) ≤ exp_{2E+q}(x)` for all `x`, which is a contradiction.
  - Suppose `F` is not amenable. Then `CR = ∞` from some point on. By clause 4 every `φ ∈ 𝓡` is `∞` from some point
    on too, since `exp_E(∞) = ∞` is the only way `exp_E(φ(exp_E x))` can bound an infinite value.
- **The primitive-recursive question is one question.** Let `φ ≈ χ` with constant `E`, and let `φ` eventually
  dominate every primitive recursive function. Take any primitive recursive `f`, and assume without loss of generality
  that `f` is nondecreasing, by passing to `max_{y≤x} f(y)`. Put `g(x) = exp_E(f(exp_E(x+1)))`, which is primitive
  recursive. For large `y`, choose `x` with `exp_E(x) ≤ y < exp_E(x+1)`. Then
  `exp_E(χ(y)) ≥ exp_E(χ(exp_E x)) ≥ φ(x) ≥ g(x) = exp_E(f(exp_E(x+1)))`, so `χ(y) ≥ f(exp_E(x+1)) ≥ f(y)`. So
  `thompson-f-folner-function-dominates-every-ackermann-level` holds for `Føl` if and only if the same statement
  holds for `R`, or for `ψ`, or for `CR`. The collapse neither proves nor refutes it.

## What is and is not new

Clause 1 is a two-line consequence of CRE(E) and degree order (3). It is recorded because SFG was still OPEN in the
graph, with no `refuted_by`, after the one-Ramsey-call theorem. Clauses 2 and 3 are standard (connected Følner
sets, and Namioka's trick after a Kesten-type smoothing), with explicit constants. The only deep input is CRE(E),
whose proof rests on the self-wreath embedding `(F ≀ Z) × Z ≤ F`. In the free group `F_2`, `R_{F_2}(1) = 3`
while `CR_{F_2}(1) = ∞` (`small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2`), so `CR ≼ R` fails there. The collapse is a property of `F`, not of the definitions.
