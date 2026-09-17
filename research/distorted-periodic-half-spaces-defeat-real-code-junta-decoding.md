---
rg: 2
id: distorted-periodic-half-spaces-defeat-real-code-junta-decoding
kind: claim
title: Distorted periodic half-spaces interval(sum sigma_i phi_a(x_i)) are folded, reject the Khot--Moshkovitz low-boundary, constraint and consistency tests within their completeness bounds O(sqrt(alpha|K|)), O(beta/sqrt k), O(delta sqrt(delta n)), yet correlate at most eta with every junta of l real code functions, so near-complete real-code strategies need not be (l, gamma)-list decodable
distinct_from:
  affine-long-code-test-has-no-uniform-soundness: that kills the folded long-code noise test over F_lin-rich outer games by an explicit low-value source with high-acceptance labelings; this is about the Khot--Moshkovitz real code over R^n and kills the list-decoding step of its soundness, not a finite-field test.
  noise-test-transparent-on-decodable-matching-features: that shows the BKM noise test is transparent on decodable features; this exhibits strategies of the real-code tests that are not decodable into bounded juntas at all.
  unique-games-hard-at-completeness-one-half: that is the unconditional 2-to-2 gap; this concerns the separate candidate route to the weak UGC through real linear equations.
  noisy-affine-selector-defeats-bounded-hitting: that defeats a bounded-hitting lemma for folded Boolean functions on F_2^n under noise; this defeats bounded-junta list decoding for folded functions on Gaussian space under the real-code tests.
artifacts:
  - experiments/real-code-distortion-2026-09-17/check_distorted_real_code.py
---

**ESTABLISHED.** Elementary Fourier analysis on Gaussian space. Proof:
`distorted-periodic-half-spaces-junta-farness-proof`.

## Setting (Khot--Moshkovitz, STOC 2016)

Khot and Moshkovitz, *Candidate hard unique game* (STOC 2016; full version at
cs.utexas.edu/~danama/papers/ugc/candidate-linear.pdf),
reduce random `kCSP(PHLin)` to approximate real linear equations and then to
Boolean 2-variable linear equations. They aim at the **weak UGC**: a
`(1 - eps, 1 - C eps)` gap. The honest encoding of `sigma in {+-1}^n` is the
**real code**

```text
f_sigma(x) = interval(<sigma, x>),     x ~ N(0, I_n),
interval(z) = +1 on [2j, 2j+1),  -1 on [2j-1, 2j)   (j in Z).
```

Strategies must be **folded**: `f(x + e_i) = -f(x)` and `f(-x) = -f(x)`. The three
tests and their completeness rates (KM Lemmas 4.1/5.2, 5.1, 6.1) are:

- **low boundary on `K`**: noise only the coordinates in `K`, correlation `1 - alpha`;
  reject iff `f(x) != f(y)`; honest rate `O(sqrt(alpha |K|))`;
- **constraint test**: move `x` along the unit vector `v_C` (entries
  `eps_j b_j / sqrt(k)` on a constraint `C` of size `k`), with correlation
  `1 - beta^2/2`; honest rate `O(beta / sqrt(k))` on Lasserre local distributions;
- **consistency test**: `f_S`, `f_R` on sets sharing coordinates, where
  non-shared coordinates are small (`|t| <= s ~ delta`); honest rate
  `O(delta sqrt(delta n))`.

KM prove soundness only for list-decoding strategies. Quoted verbatim (ASCII
transliteration):

> Definition 13. An (l, gamma)-list decoding strategy is as follows. For at least
> 1 - gamma fraction of the sets S <= [N], |S| = n, there are is a real code junta
> J_S : R^n -> {-1, 1} depending on at most l real code functions, such that
> Pr_x [f_S(x) = J_S(x)] >= 1 - gamma.

> Theorem 14 (Soundness for list decoding strategies). Let 0 < gamma < 1/4 be a
> constant and let l >= 1 be a constant. [...] With high probability over Phi, for
> any (l, gamma)-list decoding strategy, at least one of the two holds: 1. The
> consistency test rejects with probability at least Omega(sqrt(eps n)) [...]
> 2. The constraint test rejects with probability at least Omega(beta) [...]

They also state the open question on which the route depends:

> Whether the weak Unique Games Conjecture could follow (either directly from our
> analysis or from a strengthening of it) depends on whether the case addressed in
> our restricted soundness is "essentially" the only case. [...] Robust Gaussian
> Isoperimetry: Which functions fail the noise test with probability only a
> constant times larger than a (periodized) half-space? Are functions
> "influenced" by a constant number of (periodized) half-spaces the only such
> functions?

## Statement

For `a in (0, 1)` put `phi_a(t) = t + (a / 2 pi) sin(2 pi t)`, so that
`phi_a' in [1 - a, 1 + a]`, `phi_a(t + 1) = phi_a(t) + 1` and `phi_a` is odd. The
**distorted real code** is

```text
f_{sigma,a}(x) = interval( g(x) ),     g(x) = sum_i sigma_i phi_a(x_i).
```

Put `nu = 6e-9` (so the Gaussian measure mod `Z` has density in `[1 - nu, 1 + nu]`)
and `mu = e^(-2 pi^2)`. For every `sigma in {+-1}^n`:

1. **(Folding.)** `f_{sigma,a}(x + e_i) = -f_{sigma,a}(x)` and
   `f_{sigma,a}(-x) = -f_{sigma,a}(x)` for almost every `x`.
2. **(Low boundary on `K`.)** The rejection probability is at most
   `arccos(1 - alpha) sqrt(2/pi) (1 + a) sqrt(|K|) (1 + nu)/(1 - a)`, which is
   `<= sqrt(pi/2) (1 + a)(1 + nu)/(1 - a) * sqrt(alpha |K|)`. For `a = 0`, `K = [n]`
   and `alpha n <= 1/4`, the honest rate is at least
   `(1 - 3 e^(-pi^2 n)) (2 sqrt(alpha n / pi) - 2 alpha n)`.
3. **(Constraint test.)** For a constraint vector `v_C` with `k < n`, the rejection
   probability is at most
   `arccos(1 - beta^2/2) sqrt(2/pi) (1 + nu)/(1 - a) * ( |<sigma, v_C>| + a (1 + mu sqrt k) )`.
   With `a <= 1/sqrt(k)` and `E|<sigma, v_C>| = O(1/sqrt(k))` (the Lasserre local
   distributions, KM Lemma 5.1) this is `O(beta / sqrt(k))`.
4. **(Consistency test.)** If the shared coordinates have density at most
   `M gamma` and the `m` non-shared coordinates satisfy `|x_i|, |y_i| <= s`, the
   rejection probability is at most `M (1 + nu)/(1 - a) * 2 (1 + a) s sqrt(m)`. For
   `s ~ delta`, `m ~ delta n` and `M = 1/(1 - delta)` this is `O(delta sqrt(delta n))`.
5. **(Surface area.)** The Gaussian surface area of `{f_{sigma,a} = 1}` is at most
   `(1 + a)(1 + nu)/(1 - a) * sqrt(n)`. The periodic half-space `{f_sigma = 1}` has
   area `sqrt(n) sum_m e^(-2 pi^2 m^2 n) >= sqrt(n)`. The ratio tends to 1 as `a -> 0`.
6. **(Farness from every bounded junta.)** For every `a in (0, 1)`, `l >= 1` and
   `eta > 0` there is `n_0` such that for all `n >= n_0`, all `sigma`, all
   `G : {+-1}^l -> [-1, 1]` and all nonzero integer vectors `tau_1, ..., tau_l in Z^n`,
   ```text
   | E_x [ f_{sigma,a}(x) G( interval<tau_1,x>, ..., interval<tau_l,x> ) ] | <= eta.
   ```
   The same holds for `f_{sigma,a}` restricted to any subset of at least `n/2`
   coordinates (the others fixed arbitrarily). Hence `Pr[f_{sigma,a} = J] <= (1 + eta)/2`
   for every real code junta `J` on `l` functions.
7. **(Not list decodable.)** Assign to every set `S` the distorted code
   `f_{S} = f_{sigma_S,a}` of any `sigma_S` (for example the honest Lasserre
   assignment). This strategy is folded and passes the three KM tests within the
   bounds of items 2--4. For `gamma < 1/4`, `eta < 1/2` and `n >= n_0(a, l, eta)`,
   no set `S` has a junta with `Pr[f_S = J_S] >= 1 - gamma`, so the strategy is
   not `(l, gamma)`-list decodable for any constant `l`.

## What this kills, and where

**Decomposition of the KM route to the weak UGC.**

- **(P-a)** Hardness of random `kCSP(PHLin)` at the required density, and the
  Lasserre gap for `kLin(R)` (Tulsiani). These are assumptions or citations.
- **(P-b)** Completeness: honest real codes pass (KM Lemmas 4.1, 5.1, 6.1).
- **(P-c)** Soundness for `(l, gamma)`-list decoding strategies (KM Theorem 14).
- **(P-d)** *Structure:* every folded strategy whose rejection rates are within a
  constant factor of the honest rates is `(l, gamma)`-list decodable, with `l` constant.
- **(P-d') and (P-c')** A structure theorem for a class `Str` that contains the
  distorted codes, together with soundness for `Str`.

This claim **refutes (P-d)** in the form of Definition 13. It answers KM's second
Robust Gaussian Isoperimetry question negatively when "influenced" is read as
correlation with a bounded junta, which is the reading Definition 13 needs. Items 2 and 5 show functions
that fail the noise test with probability at most
`1.111 (1 + a)(1 + nu)/(1 - a) (1 + O(sqrt(alpha n)))` times the honest rate of a periodized
half-space, a constant tending to about 1.11 as `a -> 0`. By item 6 they are "influenced" by no constant number of periodized
half-spaces: their correlation with every such junta tends to 0.

- *The invariant* is the **per-coordinate Fourier contraction**
  `lambda_K(a) = sup_{odd |kappa| <= K, w in Z} |E e^(i pi (kappa phi_a(X) + w X))| < 1`
  of a 1-periodic distortion. Every term of the Fourier expansion of
  `f_{sigma,a} J` is a product over all `n` coordinates of these characters, and
  each factor has absolute value at most `lambda_K(a)`.
- *The step where every member dies* is the list-decoding step in the proof of
  KM Theorem 14: "Except with probability 2 gamma there are list decodings". Any
  soundness proof that reads a bounded list of real code functions `sigma_{S,j}`
  off a near-complete strategy dies there. The same proof works for every odd `C^2` map `phi != id` with `phi(t + 1) = phi(t) + 1`
  and `phi' in [1 - a, 1 + a]`: `kappa phi(t) + w t` is constant mod 2 only when
  `phi` is affine, and hence the identity.

**Survivor.** The distortion does not change the "effective weight"
`E_gamma phi_a'(Z) = 1 + a mu` of any coordinate. So `f_{sigma,a}` still carries the
labels `sigma_i` through the sign of the expected flux across coordinate `i`. A
repaired route needs a **reparametrization-invariant** structure theorem, (P-d').
One candidate: near-complete strategies are close to `interval(sum_i h_i(x_i))`
(or to bounded juntas of such functions) with `h_i(t + 1) = h_i(t) + sigma_i`.
It also needs a soundness analysis (P-c') in which the decoded list is a list of
sign vectors, not of functions. Both are OPEN.
The farness in item 6 uses compactness for fixed `a`. As `a -> 0` with `n` the
contraction `1 - lambda_7(a)` is numerically about `a^2 / 16` (replay, part C), so for `a << n^(-1/2)` the
distorted code is again correlated with `f_sigma`.

This neither proves nor refutes the weak UGC or UGC. It shows that the
restricted soundness of KM does not cover all near-complete strategies.

DERIVATION distorted-periodic-half-spaces-junta-farness-proof
