---
rg: 2
id: m11-balanced-loop-host-h1-is-z55-proof
kind: route
title: Proof that H_1(R°) = Z/55 by descent of e_b + e_C along sections to pure powers of b or C, and that the degree-2 Nakaoka recursion for R° = R° wr M_11 is the identity
target: m11-balanced-loop-host-h1-is-z55
requires:
  - m11-balanced-loop-host-has-finite-h1
  - fully-self-replicating-fp2-groups-have-odd-cyclic-h1
  - tits-hosts-for-transitive-local-actions
artifacts:
  - experiments/m11-balanced-loop-host-h1-2026-09-18/balanced_h1_descent_check.py
  - experiments/m11-balanced-loop-host-h1-2026-09-18/balanced_h1_descent_check.out
---

**Status: ESTABLISHED (unreviewed).** The proof is by hand. The script checks Lemmas 1–4 on
every reduced word of length at most 5, and Lemma 0 on level 4.

## Setup

Let `F` be the free group on `α, β, b, C`, and let `N` be the kernel of `F → R°`. Call
`b^{±1}` and `C^{±1}` the *f-letters*. For `w ∈ F`, write:

- `nf(w)` for the number of f-letters of `w`;
- `nC(w)` for the number of `C^{±1}` letters;
- `χ(w) = e_b(w) + e_C(w) ∈ Z`, the total exponent of the f-letters. It is a
  homomorphism, and `χ(α) = χ(β) = 0`.

For `x ∈ X`, the formal section `w|_x ∈ F` is defined by reading `w` from left to right,
starting at `x`, and concatenating the letter sections. The result is then freely
reduced. The letter sections are:

- `α^{±1}, β^{±1}`: trivial at every point;
- `b`: `b` at `1`, `α` at `2`, `β` at `3`, and trivial elsewhere;
- `C`: `C` at `4`, `bα` at `5`, `C^{−1}` at `6`, and trivial elsewhere;
- inverses read at `x` give the inverse of the section at `x`, since `b` and `C` have
  trivial root.

`w|_x` maps to the section at `x` of the image of `w`. So if `w ∈ N`, then `w|_x ∈ N` for
every `x`.

## Lemmas

**Lemma 0.** `b` has order exactly `55`.

*Proof.* `b^k = (b^k, α^k, β^k, 1, …, 1)`. If `b^k = 1`, then `α^k = 1` and `β^k = 1`, so
`55 | k`. Conversely, `b^{55} = (b^{55}, 1, …, 1)` fixes level 1. By induction on `n` it
acts trivially on level `n` for every `n`. ∎

**Lemma 1 (mass).** For every `w ∈ F`, `Σ_{x ∈ X} χ(w|_x) = χ(w)`.

*Proof.* `χ` ignores free reduction. So the left side is the sum, over the letters `t` of
`w`, of `Σ_x χ(t|_x)`: as `x` runs over `X`, each letter is read at every point exactly
once, because the prefix acts by a bijection. The inner sums are:

- `0` for `α^{±1}` and `β^{±1}`;
- `±χ(b) = ±1` for `b^{±1}`;
- `±(χ(C) + χ(bα) + χ(C^{−1})) = ±(1 + 1 − 1) = ±1` for `C^{±1}`.

This is `χ(t)` in each case. ∎

(Neither `e_b` nor `e_C` alone has this property:
`Σ_x e_b(w|_x) = e_b(w) + e_C(w)` and `Σ_x e_C(w|_x) = 0`.)

**Lemma 2 (counts).** `nf(w|_x) ≤ nf(w)` and `nC(w|_x) ≤ nC(w)`.

*Proof.* A letter read at one point contributes at most one f-letter. `C`-letters arise
only from `C`-letters, read at `4` or `6`. Free reduction only lowers the counts. ∎

**Lemma 3 (stable sections).** Suppose `nf(w|_x) = nf(w)` and `nC(w|_x) = nC(w)`. Then
every `b`-letter of `w` is read at `1`, and every `C`-letter at `4` or `6`, and `w|_x` is a
word over `{b, C}^{±1}`.

*Proof.* By equality in Lemma 2, every f-letter yields an f-letter, and every `C`-letter
yields a `C`-letter. So:

- no `b`-letter is read at `2` or `3`;
- no `C`-letter is read at `5`, since there it gives `bα`, which lowers `nC`;
- no f-letter is read outside `{1, 4, 5, 6}`, since there it gives nothing.

The remaining letter sections are `b^{±1}` and `C^{±1}`. ∎

**Lemma 4 (purity).** Let `w` be a word over `{b, C}^{±1}` containing both a `b`-letter
and a `C`-letter. Then no `x` satisfies the hypothesis of Lemma 3.

*Proof.* `b` and `C` have trivial root, so every letter of `w` is read at the same point
`x`. Lemma 3 would need `x = 1` for the `b`-letters and `x ∈ {4, 6}` for the `C`-letters. ∎

## Item 1

**Proposition 5.** `χ(N) ⊆ 55Z`.

*Proof.* Suppose `w_0 ∈ N` has `χ(w_0) ≢ 0 (mod 55)`. By Lemma 1 some `x_0` has
`χ(w_0|_{x_0}) ≢ 0`. Put `w_1 = w_0|_{x_0} ∈ N`, and continue in the same way. This gives
`w_i ∈ N` with `χ(w_i) ≢ 0 (mod 55)` for all `i`.

- By Lemma 2, `nf(w_i)` and `nC(w_i)` are non-increasing.
- They are bounded below by `0`, so both are constant from some index `i_0` on.
- By Lemma 3 applied to `w_{i_0}`, the word `w = w_{i_0+1}` lies over `{b, C}^{±1}`, and
  its section `w|_{x_{i_0+1}}` again keeps both counts.
- By Lemma 4, `w` is pure: after free reduction, `w = b^e` or `w = C^e`.

If `w = C^e`, then `C^e = 1` in `R°`. But `C` has infinite order, by item 1 of
`m11-balanced-loop-host-has-finite-h1`, so `e = 0` and `χ(w) = 0`. If `w = b^e`, then
`55 | e` by Lemma 0, so `χ(w) = e ≡ 0`. Either way this contradicts `χ(w) ≢ 0`. ∎

No stable-cycle analysis is needed, unlike Lemma 4 of
`m11-odometer-free-linear-host-h1-is-z55-squared-proof`. Here the eventually stable
words are pure powers, because the two kinds of loop letter are stable at disjoint sets
of points.

**Proof of item 1.** By Proposition 5, `χ` mod `55` defines a homomorphism
`λ : R° → Z/55`. It is onto, since `λ(b) = 1`. By item 2 of
`m11-balanced-loop-host-has-finite-h1`, `H_1(R°; Z)` is cyclic, generated by `[b]`, of
order dividing `55`. So `λ` induces `H_1(R°; Z) ≅ Z/55`. Also `λ(C) = 1 = λ(b)` gives
`[C] = [b]`, and `λ(M_11) = 0`. ∎

## Item 2

`Z/55` is finite, cyclic and of odd order. So item 3 of
`fully-self-replicating-fp2-groups-have-odd-cyclic-h1` holds. ∎

## Item 3

By item 3 of `m11-balanced-loop-host-has-finite-h1`, `R° ≅ R° ≀_X M_11`, and `M_11` acts
on `X` as the natural, 4-transitive, action. Apply Proposition 1 of
`fully-self-replicating-fp2-groups-have-odd-cyclic-h1-proof` with `H = H_*(R°; k)`. In
total degree `2`, `H_*(R° ≀ M_11; k)` is the sum of the following three terms.

- **`P`-degree 0.** This is the coinvariants of `(H^{⊗X})_2`. Its basis orbits are of two
  kinds.
  - One factor in degree `2`. These give `H_2(R°; k)`.
  - Two factors in degree `1`. These occur only if `H_1(R°; k) ≠ 0`, that is,
    `char k ∈ {5, 11}` by item 1. Then `H_1(R°; k) = k·u`, and the tensor with `u` at `x`
    and at `y` is fixed by an element of `M_11` swapping `x` and `y`, which exists by
    2-transitivity. That element acts by the Koszul sign `−1 ≠ 1` in `k`. So the
    coinvariants vanish.
- **`P`-degree 1.** This is `H_1(M_11; ⊕_x H_1(R°; k)_x)`. By Shapiro it equals
  `H_1(M_10; k) ⊗ H_1(R°; k)`, because the point stabilizer `M_10` acts trivially on its
  own factor.
  - `H_1(M_10; Z) = Z/2`, so `H_1(M_10; k) = 0` unless `char k = 2`.
  - `H_1(R°; F_2) = 0` by item 1.

  So this term is `0`.
- **`P`-degree 2.** This is `H_2(M_11; k)`. It is `0`, since `M_11` is perfect with
  trivial Schur multiplier.

So the composite `H_2(R°; k) ≅ H_2(R° ≀ M_11; k) ≅ H_2(R°; k)` has no complement. It gives
no condition on `dim H_2(R°; k)`: every cardinal is consistent with it. Any obstruction
from the homology recursion to `FP_2` would be a nonzero complement. So there is none. ∎

## Item 4

Let `p ∈ {5, 11}`. By item 1, `H_1(R°; F_p) = F_p·u`. By universal coefficients,
`H_2(R°; F_p) ⊇ Tor(Z/55, F_p) ≠ 0`. Let `v` be a nonzero class there. Then:

- the basis tensor with `u` at `x`, `v` at `y ≠ x` and `1` elsewhere has stabilizer
  `M_11`'s pointwise stabilizer of `x, y`;
- that stabilizer moves no odd factor, so the tensor's sign is `+1`.

This is item 2(i) of `fully-self-replicating-fp2-groups-have-odd-cyclic-h1`, so
`E_3(F_p) ≠ 0`. By item 1 of that node, `E_3(F_p) = 0` whenever `h_3 < ∞`. So
`dim H_3(R°; F_p) = ∞`. ∎

## Item 5

Item 5 is item 5 of `tits-hosts-for-transitive-local-actions`, applied to `R°`, with local
action `M_12 ⊇ M_11` as in `m11-balanced-loop-host-has-finite-h1`. ∎

## The script

`balanced_h1_descent_check.py` implements the letter sections above, with points
`0, …, 10`. On every one of the 22408 reduced words of length at most `5` over
`{α, β, b, C}^{±1}` it checks:

- Lemma 1 (M);
- Lemma 2 (N);
- the conclusion of Lemma 3 (S);
- Lemma 4 (P).

It reports no failures. It also finds `55` as the least `k` with `b^k` trivial on level
`3`, and checks that `b^{55}` is trivial on level `4`, in line with Lemma 0.
