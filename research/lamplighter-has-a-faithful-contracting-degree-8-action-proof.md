---
rg: 2
id: lamplighter-has-a-faithful-contracting-degree-8-action-proof
kind: route
title: The virtual endomorphism halves the radius of every element, and an ideal of lamps cannot be halved into itself, so the action is contracting and faithful
target: lamplighter-has-a-faithful-contracting-degree-8-action
requires: []
---

Notation is that of the claim. Products in `G` are `(p, t^k)(q, t^l) = (p + t^k q, t^{k+l})`. We use Nekrashevych's
dictionary (*Self-similar groups*, §2.5, §2.7):

- A virtual endomorphism `f: H -> G` of index `d`, together with a right transversal `T` of `H`, defines a
  self-similar action of `G` on the `d`-regular tree.
- In that action, for `g in G` and `r in T`, write `g r = r' h` with `r' in T` and `h in H`. Then `g` sends the
  letter `r` to `r'`, with section `f(h)`.
- The kernel of the action is the `f`-core: the largest subgroup `N ≤ H` that is normal in `G` and satisfies
  `f(N) ⊆ N` (Proposition 2.7.5).

## 0. `f_c` is a homomorphism, and every candidate is an `f_c`

The map `M -> F_2[t^{±1}]^2`, `m ↦ (A(t), B(t))`, is an additive bijection. Conjugation by `s` multiplies `m` by
`s`, which multiplies `A` and `B` by `s`. So `φ_c(m) = (1+t)A(t) + cB(t)` satisfies `φ_c(s m) = t φ_c(m)`, and
`f_c(m, s^j) = (φ_c(m), t^j)` is a homomorphism `H = M ⋊ ⟨s⟩ -> G`.

Conversely, suppose a homomorphism `f` sends `1 + s ↦ 1 + t` and `s ↦ t`. Compatibility with conjugation by `s`
forces `φ(s^j m) = t^j φ(m)`. Also `M` is generated as a `⟨s⟩`-module by `1 + s` and `t(1+s)`. So `f = f_c` with
`c = φ(t(1+s))`.

## 1. Non-injectivity (claim (3))

Take `A = c`, `B = 1 + t`. Then `m = (1+s)c(s) + t(1+s)^2` is nonzero, since its `t`-odd part is `t(1+s)^2 ≠ 0`.
And `φ_c(m) = (1+t)c + c(1+t) = 0`. So `f_c` is not injective, for every `c`.

## 2. Contraction for `c = 0`

Take the transversal `T = {(a, t^e) : a in {0, 1, t, 1+t}, e in {0, 1}}`.

- **Coset representatives.** `{0, 1, t, 1+t}` represents `F_2[t^{±1}]/(1+t)^2`. So every `(P, t^K)` lies in exactly
  one coset `(a', t^{e'}) H`, where `e' ≡ K (mod 2)` and `a' ≡ P (mod (1+t)^2)`.
- **Radius.** Let `ρ(g)`, for `g = (p, t^k)`, be the largest of `|k|` and `|i|` over the exponents `i` of `p`.
  Suppose `ρ(g) = R`.
- **The element `h`.** For `r = (a, t^e) in T`, the element `h = r'^{-1} g r` is
  `(t^{-e'}(p + t^k a + a'), t^{k+e-e'})`.
  - Its lamp `m` has exponents in `[-R-1, R+1]`.
  - Its shift is `s^j` with `2j = k + e - e'`, so `|j| ≤ (R+1)/2`.
- **The section `f_0(h)`.** Write `m_ev(s) = (1+s)A(s)` for the even part of `m`. The `s`-exponents of `m_ev` lie in
  `[-(R+1)/2, (R+1)/2]`.
  - Dividing by `1+s` gives `A` exponents in `[min, max - 1]` of those.
  - So `(1+t)A(t)` has exponents in `[min, max]` of those.
  - Hence `ρ(f_0(h)) ≤ ⌊(R+1)/2⌋`.
- **Conclusion.** `⌊(R+1)/2⌋ < R` for `R ≥ 2`, and `⌊(R+1)/2⌋ ≤ 1` for `R ≤ 1`. Hence all sections of `g` at levels
  `≥ ⌈log_2 R⌉ + 1` lie in the finite set `𝒩 = {ρ ≤ 1}`, which has 24 elements, and `𝒩` is closed under sections.
  So the action is contracting, and the generators `b, x` have finitely many states. The computed nucleus has 6
  elements (`results-adt48.txt`).

## 3. Faithfulness for `c = 0`

Let `N` be the `f_0`-core.

- **`N` has no shift.** Let `nZ` be the image of `N` in `Z = G/F_2[t^{±1}]`. Since `N ≤ H`, `n` is even, and `f_0(N)`
  has image `(n/2)Z`. Now `f_0(N) ⊆ N` forces `(n/2)Z ⊆ nZ`, so `n = 0`.
- **`N` is an ideal.** Hence `N ⊆ F_2[t^{±1}]`. Normality in `G` makes `N` an ideal `I ⊆ M`.
- **The ideal is zero.** Suppose `I ≠ 0`. Then `I = (d)`, where `d` is a polynomial with `d(0) = 1` and `deg d = D`.
  - `D ≥ 2`, since `d in ((1+t)^2)`.
  - Every nonzero element of `I` has span (largest exponent minus smallest) at least `D`.
  - The even part `d_ev` contains the exponent `0`, so it is nonzero, with `s`-span at most `D/2`.
  - Then `φ_0(d) = (1+t)A(t)` is nonzero, with span at most `D/2 < D`.
  - But `φ_0(d) in f_0(N) ⊆ I`, so its span is at least `D`. This is a contradiction.

So `N = 1`, and the action is faithful. ∎

## 4. Consequence

The action is contracting. By Nekrashevych (*Finitely presented groups associated with expanding maps*, 2018, the
FP2 input of `rover-nekrashevych-finite-presentation-criteria`), `V_8(Z/2 ≀ Z)` for this action is finitely presented.
Its commutator subgroup is simple for every self-similar action.

## 5. Machine check

- `adt48.py` builds the section map for any `c`, and `run48.py` computes the nucleus and searches for kernel elements.
- `rand48.py` follows random paths from 300 random elements of radius up to 60. Section radius drops as
  `130, 70, 35, 19, 12, 6, 3, …` for `c = 0`.
- Output is in `experiments/rn-lamplighter-finiteness-2026-09-17/results-adt48.txt`.
- For `c = 0` and `c = t` the 300 endpoints fall in the computed nucleus with at most one miss. That nucleus
  iteration is heuristic. The proof in §2 does not use it.
