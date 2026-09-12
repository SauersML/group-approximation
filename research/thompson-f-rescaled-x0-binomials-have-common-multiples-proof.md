---
rg: 2
id: thompson-f-rescaled-x0-binomials-have-common-multiples-proof
kind: route
title: Sort bumps by right endpoint; conjugates of the next bump by the current multiple share that endpoint, so nest them and absorb with t(1 + lambda t^-1 g t) = (1 + lambda g) t
target: thompson-f-rescaled-x0-binomials-have-common-multiples
requires: [thompson-f-twisted-x0-binomial-is-ore-with-every-element]
artifacts:
  - experiments/thompson-f/pl_check.py
  - experiments/thompson-f/pl_check.json
  - experiments/thompson-f/ore_census.py
  - experiments/thompson-f/ore_census_small_degrees.jsonl
---

Notation as in the target. `R` is a domain because `F` is left-orderable. Group elements are
units of `R`.

**Lemma A (restriction).** Let `H <= F` and `a, b` in `K[H]`. Then `a R ∩ b R ≠ 0` iff
`a K[H] ∩ b K[H] ≠ 0`.
- Choose representatives `S` of the right cosets `H s`. As a left `K[H]`-module,
  `R = ⊕_(s in S) K[H] s`.
- Write `u = sum_s u_s s` and `v = sum_s v_s s` with `u_s, v_s` in `K[H]`. Then `a u = b v`
  iff `a u_s = b v_s` for every `s`.
- So a nonzero solution in `R` has a nonzero component in `K[H]`, and the converse is clear.

**Lemma B (transport).** Let `psi : F_[p,q] -> F_[p',q']` be a group isomorphism with
`psi(g)` one-bump on `(p', q')`, and let `g` have support `(p, q)`. Then `g` has property O
iff `psi(g)` does, because `psi` induces a ring isomorphism of the group rings.
- Conjugation by `t` in `F` maps `F_[p,q]` onto `F_[t^-1 p, t^-1 q]`, so `O_1` is closed
  under conjugation.

**Lemma C (base cases).**
- *`x_0`.* Property O is `thompson-f-twisted-x0-binomial-is-ore-with-every-element`,
  since `F_[0,1] = F`.
- *`x_0^-1`.* `(1 + lambda x_0^-1) R = x_0^-1 (1 + lambda^-1 x_0) R`, and
  `(1 + lambda x_0^-1) R ∩ b R = x_0^-1 [(1 + lambda^-1 x_0) R ∩ x_0 b R] ≠ 0`.
- *`x_n^{+-1}`.* For `n = 1, 2, 3`, `experiments/thompson-f/pl_check.json` verifies exactly
  that `x_n` has support `(1 - 2^-n, 1)`. It also verifies that the affine map
  `sigma_n : [1 - 2^-n, 1] -> [0,1]`, of slope `2^n`, conjugates `x_n` to `x_0`. So
  `sigma_n F_[1-2^-n,1] sigma_n^-1 = F` with `x_n -> x_0`, and Lemma B applies.
  - *General `n`.* Put `tau = sigma_1^-1`, that is `y -> (y+1)/2`. From `sigma_2 = sigma_1 ∘ sigma_1`,
    `tau x_0 tau^-1 = x_1` and `tau x_1 tau^-1 = x_2`. So conjugation by `tau` agrees on
    generators with the shift endomorphism `phi(x_i) = x_(i+1)`, hence on all of `F`.
  - Then `x_n = tau^(n-1) x_1 tau^(1-n)`, with support `(1 - 2^-n, 1)`, and Lemma B applies.

**Lemma D (common right endpoint).** Let `c_1, ..., c_r` be in `O_1` with supports
`(a_i, q)` sharing `q`, and let `lambda_i` be in `K^x`. Then
`∩_i (1 + lambda_i c_i) K[F_[a,q]] ≠ 0`, where `a = min a_i`.
- Order the family so that `a_1 <= ... <= a_r`. Then
  `F_[a_r,q] ⊆ ... ⊆ F_[a_1,q]`, and `c_l` lies in `F_[a_i,q]` for `l >= i`.
- *Innermost term.* Put `y_r = 1 + lambda_r c_r`.
- *Step.* Given a nonzero `y_(i+1)` in `∩_(l > i) (1 + lambda_l c_l) K[F_[a_(i+1),q]]`,
  property O of `c_i` gives a nonzero `y_i = y_(i+1) z` in
  `(1 + lambda_i c_i) K[F_[a_i,q]]`. Right ideals absorb `z`.
- `y_1` is the required element.

**Item 1 (induction on right endpoints).** Order the family so that `q_1 <= ... <= q_m`,
with `supp g_i = (p_i, q_i)`, and put `P_j = min_(i <= j) p_i`.

*Claim.* There is a nonzero `w_j` in `∩_(i <= j) (1 + lambda_i g_i) R` with
`supp w_j ⊆ F_[P_j, q_j]`.
- *`j = 1`.* Take `w_1 = 1 + lambda_1 g_1`.
- *From `j` to `j + 1`.* Let `T = supp w_j`. Each `t` in `T` is the identity on
  `[q_j, 1]`, which contains `q_(j+1)`.
  - The conjugate `c_t = t^-1 g_(j+1) t` is in `O_1` by Lemma B, with support
    `(t^-1(p_(j+1)), q_(j+1))`, so all the `c_t` share the right endpoint `q_(j+1)`.
  - Lemma D gives a nonzero `v` in `∩_(t in T) (1 + lambda_(j+1) c_t) R` supported in
    `F_[P', q_(j+1)]`, where `P' = min_t t^-1(p_(j+1)) >= P_(j+1)`.
  - Since `t (1 + lambda c_t) = (1 + lambda g_(j+1)) t`, every `t v` lies in
    `(1 + lambda_(j+1) g_(j+1)) R`. So `w_j v = sum_t (w_j)_t t v` lies there too.
  - It lies in the earlier ideals because they are right ideals. It is nonzero because
    `R` is a domain. Its support lies in `F_[P_(j+1), q_(j+1)]`.

**Item 2.** Given `b ≠ 0` and `g` in `O_1`, the conjugates `t^-1 g t` for `t` in `supp b`
are in `O_1`. Item 1 gives a nonzero `v` in `∩_t (1 + lambda t^-1 g t) R`. As in the last
step of item 1, `b v` lies in `(1 + lambda g) R`, and `b v ≠ 0`.

**Item 3.**
- *Normal form.* Units move through products: `s (1 + lambda g) = (1 + lambda s g s^-1) s`.
  So `a = beta (1 + lambda_1 g_1) ... (1 + lambda_r g_r) s` with every `g_i` in `O_1`.
- *Induction on `r`.* Item 2 gives `b v_1 = (1 + lambda_1 g_1) y_1 ≠ 0`. Applied to `y_1`,
  it gives `y_1 v_2 = (1 + lambda_2 g_2) y_2 ≠ 0`, and so on. Then
  `b v_1 ... v_r = (1 + lambda_1 g_1) ... (1 + lambda_r g_r) y_r`, a nonzero element of
  `a R ∩ b R`.
- *Families.* Starting from one arbitrary `b` and intersecting successively with each
  product in the family gives the second statement.

**Item 4 (members).**
- *`x_1 x_0^-1`.* By item 2 applied to `x_1`, `(1 + lambda x_1) R ∩ b R ≠ 0` for all
  `lambda` and `b`. The survey's automorphism `alpha : x_0 -> x_0^-1`,
  `x_1 -> x_1 x_0^-1` (arXiv:2305.07113 §1.5, quoted) transports this to `x_1 x_0^-1`.
  - `pl_check.json` shows `x_1 x_0^-1` is one-bump on `(0, 3/4)`.
  - Lemma A restricts global torsion to `K[F_[0,3/4]]`, which is property O.
  - Its inverse follows as in Lemma C.
- *`x_0^-1 x_1`.* It equals `x_0^-1 (x_1 x_0^-1) x_0` and `x_2 x_0^-1` (the latter from
  `x_1 x_0 = x_0 x_2`, and checked in `pl_check.json`), so it is in `O_1` by conjugation.
- *`x_2 x_1^-1`.* The affine map `tau(y) = (y + 1)/2` satisfies `tau x_0 tau^-1 = x_1` and
  `tau x_1 tau^-1 = x_2`. These are Lemma C's maps: `tau = sigma_1^-1`, and
  `sigma_1 ∘ sigma_1 = sigma_2`. So conjugation by `tau` realizes the shift endomorphism
  `x_i -> x_(i+1)` on `F`.
  - It maps `F_[0,3/4]` onto `F_[1/2,7/8]` and `x_1 x_0^-1` to `x_2 x_1^-1`, which
    `pl_check.json` confirms is one-bump on `(1/2, 7/8)`.
  - Lemma B applies, and `x_1^-1 x_2 = x_1^-1 (x_2 x_1^-1) x_1` follows by conjugation.

**Item 5.** Right unit factors do not change principal right ideals.
- *`alpha, beta ≠ 0`.* `alpha x_0 + beta x_1 = alpha (1 + (beta/alpha) x_1 x_0^-1) x_0`.
- *`alpha, gamma ≠ 0`.* `alpha x_0 + gamma x_2 = alpha (1 + (gamma/alpha) x_2 x_0^-1) x_0`.
- *`beta, gamma ≠ 0`.* `beta x_1 + gamma x_2 = beta (1 + (gamma/beta) x_2 x_1^-1) x_1`.
- *Other forms.* A form with one nonzero coefficient is a unit, and a zero form makes the
  system trivially solvable: `u_0 ≠ 0`, the rest `0`.

A nonzero solution exists iff the principal right ideals of the nonzero forms have a nonzero
common element.
- *(a)* With at most one form having all three coefficients nonzero, item 3's family
  statement applies. The binomial forms are units times twisted binomials of `O_1`
  elements, and the full trinomial plays the role of the arbitrary element.
- *(b)* Over `F_2` the only form with three nonzero coefficients is `x_0 + x_1 + x_2`, so
  (a) covers every system.

**Trust surfaces.**
- Quoted: survey Lemma 3.8, `alpha` being an automorphism (survey §1.5), and
  left-orderability of `F`.
- Computed exactly: the supports and affine conjugacies in `experiments/thompson-f/pl_check.py`.
  The script checks that the right-to-left realization satisfies Guba's relations.
- Everything else is proved above.
