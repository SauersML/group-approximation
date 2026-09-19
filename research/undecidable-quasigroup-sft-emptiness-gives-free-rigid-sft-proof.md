---
rg: 2
id: undecidable-quasigroup-sft-emptiness-gives-free-rigid-sft-proof
kind: route
title: Solve the period equation F^q r = σ^(-p) r through bipermutivity to get a periodic row, stack it, and run the Wang argument
target: undecidable-quasigroup-sft-emptiness-gives-free-rigid-sft
requires: [permutive-triangle-sfts-are-quantum-rigid, small-window-quasigroup-sub-sfts-have-periodic-points, matricial-aperiodic-sft-rings-are-not-quantum-rigid]
---

Notation. `r_t` is row `t` of `x`, so `x(i,t) = r_t(i)`. `F(r)(i) = r(i) ⋆ r(i+1)` and `r_(t+1) = F(r_t)`. `σ` is
the left shift, `(σr)(i) = r(i+1)`. Write `a \ c` for the unique `b` with `a ⋆ b = c`, and `c / b` for the unique
`a` with `a ⋆ b = c`. Throughout, `Ω ⊆ X_⋆` is closed and invariant under `Z^2`.

## 1. Three stacking lemmas

**(R) Rows.** Suppose `x ∈ Ω` and `r_0` is `σ^p`-periodic, `p >= 1`. Then `Ω` has a doubly periodic point.

*Proof.* `F` commutes with `σ`, so every `r_t` with `t >= 0` lies in the finite set `P_p` of `σ^p`-periodic
words. Hence `r_(T+m) = r_T` for some `T >= 0` and `m >= 1`, and then `r_(t+m) = r_t` for all `t >= T`. Let `y_k`
be `x` translated so that row `T + km` becomes row `0`. For fixed `t` and `k >= |t|/m`, row `t` of `y_k` is
`r_(T + km + t) = r_(T + (t mod m))`. So `y_k` converges to the point `y` with rows `r_(T + (t mod m))`. Now
`y ∈ Ω`, and `y` has periods `(p, 0)` and `(0, m)`. ∎

**(C) Columns.** Let `c_i(t) = x(i,t)`. Then `c_(i+1)(t) = c_i(t) \ c_i(t+1) =: G(c_i)(t)`, and `G` commutes with
the vertical shift. If `c_0` has vertical period `q >= 1`, the argument of (R) with `G` in place of `F` gives a
doubly periodic point.

**(A) Antidiagonals.** Let `ℓ_c(i) = x(i, c-i)`. From `x(i, s+1) = x(i,s) ⋆ x(i+1,s)` with `s = c-1-i` we get
`ℓ_(c-1)(i) = ℓ_c(i) / ℓ_c(i+1) =: H(ℓ_c)(i)`, and `H` commutes with `σ`. If some `ℓ_c` is `σ^q`-periodic, the
argument of (R) with `H` and the translation `-e_2` gives a doubly periodic point.

## 2. Any period gives a periodic line (claim item 1)

Let `x ∈ Ω` satisfy `x(z+v) = x(z)` with `v = (p, q) ≠ 0`.
- If `q = 0`, row `r_0` is `σ^|p|`-periodic, so (R) applies.
- If `p = 0`, column `c_0` is vertically periodic, so (C) applies.
- If `p = -q`, `ℓ_c(i - q) = x(i-q, c-i+q) = x(i, c-i) = ℓ_c(i)`, so (A) applies.

Otherwise replace `v` by `-v` so that `q >= 1`, and put `m = -p`, so `m ∉ {0, q}`. From `x(i+p, t+q) = x(i,t)`
we get `F^q(r)(j) = r(j - p) = r(j + m)` for `r = r_0` and all `j`. Here `F^q(r)(j) = f(r(j), ..., r(j+q))`, and
`f` is a bijection in its first argument and in its last argument when the others are fixed. This holds for
`q = 1` because `⋆` is a quasigroup. For the induction, write `F^q(r)(j) = f'((Fr)(j), ..., (Fr)(j+q-1))` with `f'`
the rule of `F^(q-1)`. Only `(Fr)(j)` involves `r(j)`, as `r(j) ⋆ r(j+1)`; only `(Fr)(j+q-1)` involves `r(j+q)`.

So `r(j+m) = f(r(j), ..., r(j+q))` for all `j`. Let `I = [min(0, m), max(q, m))`, of length `N`, and
`w_j = r|(j + I) ∈ Q^N`.
- **Forward.** `r(j + max(q,m))` is a fixed function of `w_j`:
  - if `m > q`, it is `r(j+m) = f(r(j..j+q))`;
  - if `m < q`, it is `r(j+q)`, found from the equation by solving in the last argument. The other entries
    `r(j..j+q-1)` and `r(j+m)` are in `j + I`. (When `0 < m < q`, `r(j+m)` is one of them; when `m < 0`, it is
    `r(j - |m|)`.)
- **Backward.** `r(j + min(0,m))` is a fixed function of `w_(j+1)`:
  - if `m > 0`, it is `r(j)`, found by solving in the first argument from `r(j+1..j+q)` and `r(j+m)`, all in
    `j + 1 + I`;
  - if `m < 0`, it is `r(j+m) = f(r(j..j+q))`, and `j..j+q` lies in `j + 1 + I`.

So there are fixed maps with `w_(j+1) = Φ(w_j)` and `w_j = Ψ(w_(j+1))` for all `j`. Since `Q^N` is finite,
`w_a = w_b` for some `a < b`. Applying `Φ` and `Ψ` gives `w_(a+k) = w_(b+k)` for all `k ∈ Z`, so `r_0` is
`σ^(b-a)`-periodic and (R) applies.

Hence a point with any nonzero stabilizer forces a doubly periodic point. A doubly periodic point has a nonzero
stabilizer. This gives the equivalences of item 1. ∎

## 3. The dichotomy (claim item 2)

The input is a Latin square `⋆` on `Q` together with a finite `A ⊆ Q^L`.

**Emptiness is semi-decidable.** Let `Y = {r ∈ Q^Z : every length-L word of F^t r lies in A, for all t >= 0}`.
If `x ∈ Ω(⋆, A)` then `r_0 ∈ Y`. Conversely, if `r ∈ Y`, let `x^(k)` be the point whose rows `-k, -k+1, ...` are
`r, Fr, ...`, extended arbitrarily below. A limit point of `x^(k)` lies in `Ω(⋆, A)`. So `Ω(⋆, A) = ∅` iff `Y = ∅`.

Now `Y = ∩_T Y_T`, where `Y_T` is the one-dimensional SFT with allowed words of length `L + T` being those `w`
whose images `F^t w` (`t <= T`, each a word of length `L + T - t`) have all length-`L` subwords in `A`. The sets
`Y_T` are compact and decreasing, so `Y = ∅` iff some `Y_T = ∅`. Emptiness of a one-dimensional SFT is decidable,
since it is emptiness of the cycle set of a finite de Bruijn graph. Enumerating `T` semi-decides `Ω(⋆, A) = ∅`.

**Under (D), nonemptiness is semi-decidable.** Enumerate pairs `(p, m)` of positive integers and test the finitely
many `σ^p`-periodic rows `r` with `F^m r = r` such that the length-`L` words of `r, Fr, ..., F^(m-1) r` all lie
in `A`. Any such `r` stacks, with rows `F^(t mod m) r`, to a point of `Ω(⋆, A)`. Under (D) every nonempty `Ω(⋆, A)` has a doubly periodic point, whose row `0` is such an `r`.

Running both searches together decides emptiness. If (D) fails, some nonempty `Ω = Ω(⋆, A)` has no periodic
point, so by item 1 it is free. It is an SFT in which any two of `x(z)`, `x(z+e_1)`, `x(z+e_2)` determine the third,
so by `permutive-triangle-sfts-are-quantum-rigid` it is quantum rigid and `LC(Ω, k) ⋊ Z^2` is finitely presented.
That is (F). (D) and (F) exclude each other, since (F) exhibits a nonempty example with no periodic point. ∎

## 4. Item 3

This is the contrapositive of (D) ⇒ decidable, followed by (F). Since `Ω` is free, it is aperiodic. With `R_Ω`
finitely presented, `matricial-aperiodic-sft-rings-are-not-quantum-rigid` (item 2, contrapositive) says `R_Ω` does
not embed unitally in an ultraproduct of matrix algebras. ∎

**Dependency note.** Item 2 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid` is marked unreviewed there.
Items 1 and 2 of this claim do not use it.
