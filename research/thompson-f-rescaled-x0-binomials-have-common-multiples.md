---
rg: 2
id: thompson-f-rescaled-x0-binomials-have-common-multiples
kind: claim
title: In K[F], twisted binomials of one-bump elements that behave like x_0 on their bump have common right multiples with each other and with any one element, which settles Guba's Q_k over F_2
distinct_from:
  thompson-f-one-minus-x1-is-ore-with-every-element: that handles families with nested supports (p, 1) and augmentation binomials; this handles one-bump elements with arbitrary, overlapping supports, twisted binomials, products of them, and the systems Q_k.
  thompson-f-twisted-x0-binomial-is-ore-with-every-element: that is the single element x_0 against every element; this propagates it to every one-bump element with property O and to arbitrary finite families.
  thompson-f-binomial-pairs-have-common-multiples: that settles pairs (1 - a, 1 - c) through no free subgroups; this settles unboundedly many twisted binomials at once, for the one-bump class.
---

**ESTABLISHED.** Let `K` be a field and `R = K[F]`, with `F` acting on `[0,1]` by the
standard PL maps (right-to-left composition; `experiments/thompson-f/pl_check.json`).
- For dyadic `p < q`, let `F_[p,q]` be the subgroup of elements that are the identity
  outside `(p, q)`.
- A **one-bump element** is some `g` in `F` whose support is a single interval `(p, q)`.
- Such a `g` has **property O** if, for every `lambda` in `K^x` and every nonzero `b` in
  `K[F_[p,q]]`, `(1 + lambda g) K[F_[p,q]] ∩ b K[F_[p,q]] ≠ 0`.
- Write `O_1` for the set of one-bump elements with property O.

1. **Families.** For all `g_1, ..., g_m` in `O_1` and `lambda_i` in `K^x`,
   `∩_i (1 + lambda_i g_i) R ≠ 0`. The supports may overlap arbitrarily.
2. **Global torsion.** For `g` in `O_1`, `lambda` in `K^x` and nonzero `b` in `R`,
   `(1 + lambda g) R ∩ b R ≠ 0`.
3. **Products.** If `a` is a unit times a finite product of twisted binomials
   `1 + lambda g` with `g` in `O_1`, then `a R ∩ b R ≠ 0` for every nonzero `b`. Also, any
   finite family consisting of one arbitrary nonzero element and such products has a
   nonzero common right multiple.
4. **Members.** `O_1` is closed under `F`-conjugation. It contains:
   - `x_0^{+-1}`;
   - `x_n^{+-1}` for `n >= 1`, supported on `(1 - 2^-n, 1)`;
   - `x_1 x_0^-1`, supported on `(0, 3/4)`, and its inverse;
   - `x_0^-1 x_1 = x_2 x_0^-1`, supported on `(0, 7/8)`;
   - `x_2 x_1^-1`, supported on `(1/2, 7/8)`, and `x_1^-1 x_2`, supported on `(1/2, 15/16)`.
5. **Guba's Problem `Q_k`** (survey arXiv:2305.07113 §3; arXiv:2201.02308 §2). Consider
   `(alpha_0 x_0 + beta_0 x_1 + gamma_0 x_2) u_0 = ... = (alpha_k x_0 + beta_k x_1 + gamma_k x_2) u_k`.
   - (a) It has a nonzero solution whenever at most one of the `k + 1` forms has all three
     coefficients nonzero. This holds over every field.
   - (b) Over `K = F_2`, `Q_k` has a nonzero solution for every `k` and every choice of
     coefficients.

**Consequence for the roots.** A non-Ore witness for `thompson-f-is-not-amenable` needs
both sides outside the class in item 3. A negative instance of `Q_k` needs at least two
forms with all coefficients nonzero, over a field other than `F_2`. Guba names `Q_4` over
general fields as a possible negative candidate. Item 5(b) excludes it over `F_2`, and
5(a) excludes every instance with at most one full trinomial. In arXiv:2201.02308 Guba
also wrote that "one can expect a negative answer for a homogeneous polynomial b of
sufficiently high degree" for the `1 - x_1` question; item 2 says no such `b` exists.

**Scope.**
- Items 1–3 are elementary consequences of
  `thompson-f-twisted-x0-binomial-is-ore-with-every-element`, together with
  `t (1 + lambda t^-1 g t) = (1 + lambda g) t` and freeness of `K[F]` over `K[F_[p,q]]`.
- The supports in item 4 were computed exactly (`experiments/thompson-f/pl_check.py`).
- Not covered: one-bump elements with other germ slopes, and elements with several bumps.
- The small-degree census `experiments/thompson-f/ore_census_small_degrees.jsonl` finds
  no solution of `Q_4`-type systems over `F_2` in degree 4 with letters `<= 7`. So the
  solutions guaranteed by 5(b) have higher degree.
- Novelty: see `thompson-f-one-minus-x1-is-ore-with-every-element` for the literature
  check.

Proof route: `thompson-f-rescaled-x0-binomials-have-common-multiples-proof`. Artifact:
`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md`.
