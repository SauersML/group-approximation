---
rg: 2
id: v-rank-order-char-cycles-are-trivial-plus-regular
kind: claim
title: In characteristic p every rank function on F[V] gives each clopen p-cycle the Jordan profile rk((1 - [s])^j) = (1 - phi_V)(p - j)/p for 1 <= j <= p
distinct_from:
  v-rank-models-are-trivial-plus-free-on-odd-cycle-trees: that is the torsion law for odd primes different from the characteristic, where group algebras of cycle trees are semisimple; this is the characteristic prime itself, where 1 - [s] is nilpotent and the profile is p-sensitive.
  char-uniform-identities-cannot-force-v-rank-triviality: that proves a gate proof must use a p-sensitive identity; this proposes the first p-sensitive structure theorem such a proof could build on.
artifacts:
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

**OPEN.** Let `char F = p > 0`, `rk` a Sylvester matrix rank function on `F[V]`, and `phi_V = 1 - rk col(1 - [s_i])`
over a generating set. The claim: for every clopen `p`-cycle `s` and `1 <= j <= p`,

```text
rk((1 - [s])^j) = (1 - phi_V)(p - j)/p.
```

At `j = 0` the rank is `1`. Equivalently, the drops `d_i = rk((1 - [s])^i) - rk((1 - [s])^(i+1))` are
`d_0 = phi_V + (1 - phi_V)/p` and `d_i = (1 - phi_V)/p` for `1 <= i < p`: weight `phi_V` of the trivial module plus
weight `1 - phi_V` of the regular module `F[Z/p]`.

**Why it matters.**
- **`p`-sensitive.** `char-uniform-identities-cannot-force-v-rank-triviality` shows a proof of V's rank gate must use
  a `p`-sensitive identity. The nilpotency `(1 - [s])^p = 0` of clopen `p`-cycles is the natural one.
- **What the law does.** It is the `p = char F` analogue of the torsion law. The augmentation and sofic values satisfy
  it, while over `C` the von Neumann values `(p - 1)/p` for all `j >= 1` break the pattern. So it separates
  characteristic `p` from characteristic `0`.
- **What it doesn't do.** It doesn't imply the gate.

## Attempts

- **Proved on paper** (w5-v-nonamenable, artifact Proposition 4.2). With `y = 1 - [s]` and
  `d_i = rk(y^i) - rk(y^(i+1))`:
  - **(a)** `rk(y^j)` doesn't depend on the clopen `p`-cycle, since all are conjugate.
  - **(b)** `d_0 >= ... >= d_(p-1) >= 0` and `sum d_i = 1`, by the Frobenius inequality
    `rk(ABC) + rk(B) >= rk(AB) + rk(BC)` together with `y^p = 0`.
  - **(c)** `rk(y^j) <= (p - j)/p` and `rk(y) <= 1 - phi_V`, the second because `1 - [s]` is a combination of the
    `1 - [s_i]`. Averaging the last `p - j` of `d_1, ..., d_(p-1)`, whose sum is `rk(y)`, gives
    `rk(y^j) <= (1 - phi_V)(p - j)/(p - 1)` for `j >= 1`.
  - **(d)** The augmentation values (`phi_V = 1`) and the sofic values `1 - j/p` (the law with `phi_V = 0`) satisfy
    the law.
  - **What's missing:** the lower bound `rk(y^j) >= (1 - phi_V)(p - j)/p` and the sharper upper bound. (b) and (c)
    give only `rk(y^j) <= min((p - j)/p, (1 - phi_V)(p - j)/(p - 1))` for `j >= 1`.
- **Single-level data don't force it** (artifact Section 4, for `p >= 3`). On `F_p[(Z/p)^r]/m^2` every nonidentity
  element has Jordan type `[2, 1^(r-1)]`, with normalized ranks `1/(r+1)` and `0`, the same at one level. This
  normalization isn't compatible across the tree embeddings `E_r ⊆ E_(r')` inside `V`. So a proof has to use
  compatibility across levels or depth-changing elements.
- **Next test.** Decide whether a rank function on `F_p[E_infinity]` can be invariant under every disjoint-support
  endomorphism (each basis cycle mapped to a product of cycles with disjoint index sets) without being trivial plus
  regular. Every clopen `p`-cycle tuple of this shape is jointly conjugate in `V`. In characteristic `2` the relevant
  identity is `rk(x_1 + x_2) = rk(x_1)` for `x_i = 1 + [t_i]` with disjoint transpositions `t_i`.
- **Correction** (w5-v-nonamenable, after 27fa7efbff). The first version stated the law for `0 <= j <= p`. That fails
  at `j = 0` whenever `phi_V > 0`, the augmentation rank included, since `rk(y^0) = 1`. The range is `1 <= j <= p`.
