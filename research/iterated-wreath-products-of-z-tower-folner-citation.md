---
rg: 2
id: iterated-wreath-products-of-z-tower-folner-citation
kind: route
title: Import Erschler's wreath-product Følner formula, read in Stankov's verbatim restatement, and induct on the nesting depth
target: iterated-wreath-products-of-z-have-tower-folner-functions
requires: []
---

## Import

**Source actually read.** B. Stankov, *Exact descriptions of Følner functions
and sets on wreath products and Baumslag-Solitar groups*, arXiv:2111.09158v2
(26 Dec 2022), introduction, p. 2. It was read on 2026-09-18.

Verbatim, with the PDF's math rendered as text:

> "Later the Følner functions of wreath products with certain regularity
> conditions are described by Erschler [6] up to asymptotic equivalence.
> Specifically, say that a function f verifies property (*) if for all C > 0
> there is k > 0 such that f(kn) > Cf(n). The result of [6] than states that if
> the Følner function of a group A verifies property (*) (for some fixed
> generating set), then for any non-trivial group B, the Følner function of
> A ≀ B is Føl_{A≀B}(n) = Føl_B(n)^{Føl_A(n)}."

Here [6] is A. Erschler, *On Isoperimetric Profiles of Finitely Generated
Groups*, Geom. Dedicata 100(1) (2003) 157–171. That primary paper is paywalled
and was **not** opened.

Stankov's conventions, from the same pages:
- Asymptotic equivalence is defined verbatim: "Two functions are asymptotically
  equivalent if there are constants A and B such that f(x/A)/B < g(X) <
  f(xA)B." So the displayed `=` means `≃`.
- He writes the lamplighter as `Z ≀ Z/2Z`. So in `A ≀ B` the **first factor is
  the acting group** and `B` is the lamp group.

Translated to the convention of the target (lamp group first):

```text
(E)  If F_A has property (*) and L ≠ 1, then F_(L wr A)(n) ≃ F_L(n)^(F_A(n)).
```

## Derivation

**Two facts about Z.**
- `F_Z(n) = n` for the generator `±1`. An `n`-Følner set has
  `|Ω \ (Ω+1)| >= 1`, since `max Ω` is not in `Ω+1`, so `|Ω| >= n`. An interval
  of length `n` attains this.
- `F_Z` has (*): take `k = ⌈C⌉ + 1`.

**(*) propagates.** Suppose `f = F_(W_(k+1))`, and by (E) with `A = W_k`
(assuming (*) for `F_(W_k)`)

```text
h(n/A)/B < f(n) < B h(An),    where h(m) = m^(g(m)) and g = F_(W_k) >= 1.
```

`g` is non-decreasing, so for `M >= 1` we have
`h(AMn) >= M^(g(An)) (An)^(g(An)) >= M h(An)`. Take `K = A^2 M` with
`M > C B^2`. Then

```text
f(Kn) > h(AMn)/B >= M h(An)/B > C B h(An) > C f(n).
```

So `f` has (*), and by induction every `F_(W_k)` has (*). Hence (E) applies at
every level.

**Tower bound (T).** Følner functions are non-decreasing, so real arguments may
be read as floors; this changes only the constants.
- *k = 1.* (E) gives `F_(W_2)(n) > (n/A)^(n/A) / B >= 2^(n/A) / B` for
  `n >= 2A`. That is `>= 2^(n/(2A))` once `2^(n/(2A)) >= B`. So `c_1 = 2A`.
- *Step.* Suppose `F_(W_k)(m) >= exp_(k-1)(m/c_(k-1))` for `m >= n_(k-1)`. For
  `n/A >= max(2, n_(k-1))`,

  ```text
  F_(W_(k+1))(n) > (n/A)^(F_(W_k)(n/A)) / B >= 2^(exp_(k-1)(n/(A c_(k-1)))) / B
                 = exp_k(n/(A c_(k-1))) / B.
  ```

  For `k >= 1`, `exp_k(x)/B >= exp_k(x/2)` once
  `exp_(k-1)(x) - exp_(k-1)(x/2) >= log_2 B`. The left side is at least `x/2`.
  So `c_k = 2A c_(k-1)` works, and `n_k` is large enough.

**Not `≼ exp_k`.** By (T), `F_(W_(k+2))(n) >= exp_(k+1)(n/c)` with
`c = c_(k+1)`. Fix `C`.
- By induction on `j >= 1`, for every constant `a` we have
  `exp_j(n/c) > exp_(j-1)(Cn) + a` for large `n`.
  - *j = 1.* `2^(n/c) > Cn + a` for large `n`.
  - *Step.* `exp_(j+1)(n/c) > 2^a exp_j(Cn) >= exp_j(Cn) + a'` once
    `2^a - 1 >= a'`.
- Taking `j = k+1` and `a = log_2 C` gives
  `exp_(k+1)(n/c) > C exp_k(Cn)` for large `n`, when `k >= 1`.
- For `k = 0` it is `2^(n/c) > C^2 n`.

`∎`

**Membership in `B_A`** is quoted from
`permutational-boone-higman-closed-under-wreath-products`, whose special cases
list "Iterated wreath products such as `Z wr (Z wr (Z wr Z))`". It needs `Z` in
`B_A` and one application of the closure per level. It is used by the consumer
`folner-separators-of-boone-higman-proof`, which lists that node itself as a
prerequisite.

**Residual risk.** (E) is taken from a faithful secondary restatement, not from
Erschler's paper. If Erschler's hypotheses differ, only (E) changes. The
consumer needs only the lower bound, for one fixed family, at each fixed height.
