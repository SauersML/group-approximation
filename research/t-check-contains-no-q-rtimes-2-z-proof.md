---
rg: 2
id: t-check-contains-no-q-rtimes-2-z-proof
kind: route
title: Positive-mass dyadic cells have boundary values in the 2-power preimage of a finite set, and differences of such sets contain only boundedly many odd denominators, so the doubling semiconjugacy admits only rational translations of bounded odd denominator
target: t-check-contains-no-q-rtimes-2-z
requires:
  - q-x2-z-in-t-check-has-a-doubling-semiconjugacy
---

Lane proof (bh-free-16, 2026-09-18), elementary and self-contained apart from the doubling semiconjugacy.
Notation as in the claim. `o(r)` is the odd part of the denominator of a rational `r`, computed mod 1.

## Step 0. The semiconjugacy, for every 2-divisible A

Let `φ : G_A → T-check` be injective, `D = φ(A)` and `t = φ(t)`, so `t q t^-1 = q^2` for `q ∈ D`.
Run `q-x2-z-in-t-check-has-a-doubling-semiconjugacy-proof` with one change: in Step 1 there, let `m` range over powers of 2.
- **χ vanishes.** `χ(q) = χ(q^2) = 2χ(q)` gives `χ(D) = 0`, so `D <= T-bar_∞`, and `ρ|_D : D → Q` is a
  homomorphism (F1, F2 there).
- **ρ is nonzero.** The fixed-point argument there needs roots `e^m = q` in `D` only for `m = 2^k`. These exist
  since `A` is 2-divisible, and they force the slope exponent `α` to be divisible by every `2^k`, so `α = 0`.
- **ρ is injective.** A nonzero homomorphism from a rank-one torsion-free group to `Q` is injective. So
  `ρ(D) ≅ A`, and `2ρ(q) = 2^j ρ(q)` gives `j = 1`.
- **The rest is verbatim.** Steps 2 and 3 there use only `t = gδ` and F1. After conjugating by a power of `δ`,
  they give a continuous, non-decreasing, onto `h : R → R` with `C := sup|h − id| < ∞` and
  ```
  h(x+1) = h(x) + 1,    h ∘ t = δ ∘ h,    h ∘ q = h + ρ(q)   (q ∈ D).
  ```

## Step 1. Tameness

**Every `f ∈ T-check` is tame dyadic.**
- Write `f = g δ^j` with `g ∈ δ^k T-bar δ^-k`. Then `g` commutes with `τ_(2^k)`, and
  `f(x + 2^(k−j)) = f(x) + 2^k`. So the breakpoints of `f` form a discrete subset of `Z[1/2]` that is
  periodic modulo `P = 2^(k−j)`, and there are finitely many affine pieces modulo `P`.
- So all breakpoints lie in `2^(-n_1) Z` for some `n_1`. On each piece `f(x) = 2^m x + b`, with `b ∈ Z[1/2]`,
  since `f` preserves `Z[1/2]`.
- Translating a piece by `P` changes `b` by `2^k − 2^m P`. So all `b` lie in one `2^(-n_2) Z`, and `m <= m_max`.
- A dyadic interval `[j 2^-n, (j+1) 2^-n]` with `n >= n_1` contains no breakpoint in its interior. Its image is
  `[2^(m−n) j + b, 2^(m−n)(j+1) + b]`, which is dyadic once `b ∈ 2^(m−n) Z`, that is, once
  `n >= m_max + n_2`.
- So `N(f) = max(n_1, m_max + n_2)` works.

## Step 2. Boundary values of positive-mass cells

Let `N = N(t)`. For a dyadic interval `I = [a, b]` put `μ(I) = h(b) − h(a) >= 0`, and set
```
E = { h(x) mod 1 : x ∈ 2^-N Z },     P_E = { y ∈ R/Z : 2^k y ∈ E for some k >= 0 }.
```
`E` is finite, with at most `2^N` points, because `h(x+1) = h(x) + 1`.

**Claim 1.** If `μ(I) > 0`, then `h(a) mod 1` and `h(b) mod 1` lie in `P_E`.

*Proof.*
- **Large intervals.** If `|I| > 2^-N`, then `|I| >= 2^(−N+1)`, so `a, b ∈ 2^-N Z` and `h(a), h(b) ∈ E`.
- **The chain.** Otherwise put `I_0 = I` and, while `|I_j| <= 2^-N`, let `I_(j+1) = t(I_j)`. By Step 1 this is a
  dyadic interval, and `t` is increasing, so it maps endpoints to endpoints.
- **Masses double.** `h(t(x)) = 2h(x)` gives `h(I_(j+1)) = 2·h(I_j)`, so `μ(I_j) = 2^j μ(I)`.
- **The chain stops.** While `|I_j| <= 2^-N` we have `μ(I_j) <= |I_j| + 2C <= 2^-N + 2C`. Since `μ(I) > 0`,
  there is a first `k` with `|I_k| > 2^-N`.
- **Conclusion.** The endpoints `a_k, b_k` of `I_k` lie in `2^-N Z`, and `h(a_k) = 2^k h(a)`,
  `h(b_k) = 2^k h(b)`. So `2^k h(a)` and `2^k h(b)` lie in `E` mod 1. ∎

Intervals of `μ`-mass zero, which lie inside the blown-up fibres of `h`, never enter.

## Step 3. Translations move boundary values inside P_E

Let `q ∈ D` and `s = ρ(q)`.
- **A small positive-mass interval.** `h` is onto, so some `x_0` has no neighbourhood on which `h` is constant.
  For `n` large, one of the two dyadic intervals of length `2^-n` meeting at or containing `x_0` has `μ > 0`.
  Take such an `I = [a, b]` with `|I| <= 2^(−N(q))`.
- **Its image.** By Step 1, `q(I) = [q(a), q(b)]` is a dyadic interval, and
  `μ(q(I)) = h(q b) − h(q a) = μ(I) > 0`.
- **Apply Claim 1 to `I` and `q(I)`.** Both `h(a)` and `h(q(a)) = h(a) + s` lie in `P_E` mod 1.

So `s mod 1 ∈ P_E − P_E`.

## Step 4. Arithmetic of P_E − P_E

**Claim 2.** There is an odd `M` with `(P_E − P_E) ∩ Q/Z ⊆ (1/M) Z[1/2] / Z`.

*Proof.*
- **Reduction.** Let `r = y − y'` be rational, with `2^k y ≡ e_1` and `2^(k') y' ≡ e_2` (`e_i ∈ E`). Put
  `K = max(k, k')`. Then `2^K r ≡ 2^a ẽ_1 − 2^b ẽ_2 (mod 1)`, where `a = K − k`, `b = K − k'`, and
  `ẽ_i ∈ [0,1)` are lifts. Since `o(2^K r) = o(r)`, it suffices to bound `o(v)` over the rational values
  `v = 2^a ẽ_1 − 2^b ẽ_2`, for each ordered pair `(e_1, e_2) ∈ E^2`.
- **Both rational.** Then `o(v)` divides `o(ẽ_1) o(ẽ_2)`.
- **Exactly one rational.** Then `v` is irrational for all `a, b`.
- **Both irrational.** Suppose `(a, b)` and `(a', b')` both give rational values.
  - If `a − b ≠ a' − b'`, then the determinant `2^(a'+b) − 2^(a+b')` of the system is nonzero, so `ẽ_1` and `ẽ_2`
    are rational. That is a contradiction.
  - So all such pairs share `c = a − b`. Fix one, `(a_0, b_0)`, with rational value `v_0`. Every other has the form
    `(a_0 + i, b_0 + i)` with `i ∈ Z`, and value `2^i v_0`, so `o(v) = o(v_0)`.
- **Conclusion.** Take `M` to be the lcm of these finitely many bounds. ∎

## Step 5. Conclusion

- **Denominators are bounded.** By Steps 3 and 4, `ρ(D) ⊆ (1/M) Z[1/2]`.
- **So `A ≅ Z[1/2]`.** `ρ(D) ≅ A` is a nonzero 2-divisible subgroup of `(1/M) Z[1/2] ≅ Z[1/2]`. Every element
  has finite `p`-height for each odd `p`, and height `0` at all but finitely many `p`. So its type is that of
  `Z[1/2]`, and `A ≅ Z[1/2]` (Baer's classification of rank-one torsion-free groups).
- **The converse** is `<τ_1, δ> = BS(1,2)`.
- **Item 2 of the claim.** `Q`, `Z[1/6]` and `Z[1/2, 1/p]` are 2-divisible and not `≅ Z[1/2]`. `Z[1/6] x| Z^2`
  contains `Z[1/6] x|_2 Z`, and `Aff(Q) ⊇ Q x|_2 Z`. ∎

## Remarks

- **Nothing is used about the fibres of `h`.** So the minimal case (`h` a homeomorphism) and the blown-up
  case of `q-x2-z-in-t-check-blows-up-the-doubling-fixed-point` are handled together.
- **General form.** Steps 2–4 use only the hypotheses of the lemma in the claim. They need `t` and `q` tame
  dyadic, `h` monotone with `h(x+1) = h(x) + 1`, `h t = 2h` and `h q = h + s`. For a radix `d`, replace `2` by
  `d` and odd parts by `d`-free parts.
- **Calibration.**
  - `D = Z[1/2]` translations with `t = δ` gives `h = id`, `E ⊆ Z[1/2]/Z` and `M = 1`. No contradiction, as it
    should be.
  - The lemma bounds denominators, not primes: `Z[1/6] x|_2 Z` is excluded because `o(3^-k) = 3^k` is
    unbounded. A bounded odd part is allowed, for example `D = (1/3) Z[1/2]`, and that is still
    `BS(1,2)` abstractly. The 3-adic part of `Z[1/6] x| <2>` in `2V_(BS(1,3))`
    (`affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`) comes from a second radix, which the lemma does not
    see.
