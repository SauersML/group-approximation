---
rg: 2
id: higman-order-2e-models-need-exponential-rank-proof
kind: route
title: Proof by the 2-adic valuation of 3^N - 1, the eigenvalue orbit of x -> x^3 (Jordan decomposition in characteristic 2), and GAP computation of monolithic quotients of ANUPQ 2-quotients
target: higman-order-2e-models-need-exponential-rank
requires:
  - higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10
artifacts:
  - experiments/higman-monolithic-models-2026-09-18/pqgap.sh
  - experiments/higman-monolithic-models-2026-09-18/mono3.g
  - experiments/higman-monolithic-models-2026-09-18/run4-output.txt
  - experiments/higman-monolithic-models-2026-09-18/run6-output.txt
---

Notation is that of the target. Items 1–4 are proved in full here. Item 5 is a computation and its
tier is **computed**. The route requires the w15 node only for context: it certifies that models of
level `e` exist for `e <= 10`, so items 1–4 are not vacuous there.

**Lemma (valuation).** For `N >= 1`, `v_2(3^N - 1) = 1` if `N` is odd and `v_2(N) + 2` if `N` is even.
*Proof.* For odd `N`, `3^N - 1 = 2 (3^(N-1) + ... + 1)` and the bracket is a sum of `N` odd terms,
so it is odd. For `N = 2^s t` with `s >= 1` and `t` odd, use `3^(2M) - 1 = (3^M - 1)(3^M + 1)` and
induct on `s`. The case `s = 1` is `v_2(3^(2t) - 1) = v_2(3^t - 1) + v_2(3^t + 1) = 1 + 2`, since
`3^t = 3 mod 8` for odd `t`. For `s >= 2`, `3^M + 1 = 2 mod 4` with `M = N/2` even, so each doubling
adds 1. ∎

**Item 1.** Suppose `x^-1 y x = y^3`. Then `x^-N y x^N = y^(3^N)` for all `N >= 1`.
- If `x` has finite order `N`, then `y = y^(3^N)`, so `ord(y)` divides `3^N - 1`. In particular
  `y` has finite order.
- So if `ord(y)` is infinite, `ord(x)` is infinite and the claim holds by convention.
- Otherwise `2^f | 3^N - 1` with `f >= 2`. By the lemma `N` is even and `v_2(N) + 2 >= f`, so
  `2^(f-2) | N`.

Apply this three times around the cycle:
- `a^d = a^3` with `f = e` gives `2^(e-2) | ord(d)`;
- `d^c = d^3` with `f = e-2` gives `2^(e-4) | ord(c)`, when `e - 2 >= 2`;
- `c^b = c^3` with `f = e-4` gives `2^(e-6) | ord(b)`, when `e - 4 >= 2`. ∎

**Item 2.** Let `N` be the order of `A = rho(a)`, `2^e | N`, and `D = rho(d)`, so
`D^-1 A D = A^3`.

*Characteristic not 2.*
- `T = A^(N/2^e)` has order exactly `2^e`. That is prime to `char K`, so `T` is diagonalizable over
  the algebraic closure, with eigenvalues that are `2^e`-th roots of unity.
- Some eigenvalue `zeta` is a primitive `2^e`-th root of unity; otherwise `T^(2^(e-1)) = 1`.
- `T` is a power of `A`, so `D^-1 T D = T^3`. Hence `T` and `T^3` have the same eigenvalues with
  multiplicity, and `lambda -> lambda^3` maps the spectrum of `T` into itself.
- So `zeta^(3^k)` is an eigenvalue for every `k`. For `e >= 3` the class of 3 has order `2^(e-2)` in
  `(Z/2^e)^*`, because `v_2(3^(2^j) - 1) = j + 2` by the lemma. So these are `2^(e-2)` distinct
  eigenvalues, and `n >= 2^(e-2)`.

*Characteristic 2.*
- Write `A = S U` (Jordan decomposition), with `S` semisimple, `U` unipotent, `SU = US`. `A` has
  finite order, so `S` has odd order and `U` has 2-power order, and `ord(A) = ord(S) ord(U)`.
  Hence `ord(U) >= 2^e`.
- Put `U = 1 + M` with `M^n = 0`. In characteristic 2, `U^(2^j) = 1 + M^(2^j)`.
- `U^(2^(e-1)) != 1` forces `M^(2^(e-1)) != 0`, so `2^(e-1) < n`. ∎

**Item 3.** Let `Q` be a model of level `e`.
- `D`-conjugation maps `a` to `a^3`, so `d` normalizes `<a>` (of order `2^e`) and induces on it the
  automorphism `x -> x^3`, of order `2^(e-2)`.
- Let `C` be the centralizer of `<a>` in `<a, d>`. It contains `<a>`, and `<a,d>/C` embeds in
  `Aut(<a>)` and contains the image of `d`. So `|Q| >= |<a,d>| = |C| [<a,d> : C] >= 2^e 2^(e-2)`.
- The regular complex representation is faithful, so some irreducible constituent does not kill
  `a^(2^(e-1))`. In that constituent `a` has order `2^e`, and item 2 gives degree `>= 2^(e-2)`. ∎

**Item 4.** Suppose `Q_i` is a model of level `e_i -> oo` with `Q_i <= GL_n(K_i)`. Item 2 applied to
the inclusion gives `n >= 2^(e_i - 2)` for all `i`, which is impossible for fixed `n`.

For `GL_n(Z/p^j)` with `p` odd: the kernel of reduction to `GL_n(F_p)` is a `p`-group. So the involution
`a^(2^(e-1))` survives the reduction, `a` keeps order `2^e` in `GL_n(F_p)`, and the field case
applies.

The p-adic analytic case is the w10 dead end. There each generator is quasi-unipotent, since its
eigenvalues form a finite set closed under cubing. If a power `v = b^s` were a nontrivial
unipotent, `X = log v` would satisfy `Ad(a^-1) X = 3X`. But `3` is not a root of unity, while the
eigenvalues of `Ad(a^-1)` are. So the generators are torsion and their orders in the finite images
are bounded. ∎

**Item 5 (computed).**
- `pqgap.sh` runs the standalone ANUPQ with the presentation of `Gammabar_e` and exports the class-`k`
  quotient in GAP pc format (`p3.g`, `p4.g`, `p5.g`, with `(e,k) = (3,3), (4,4), (5,7)`).
- `mono3.g` repeatedly does the following while `Omega_1(Z(Q))` has rank at least 2:
  - chooses a random linear form `f` on `Omega_1(Z(Q))` with `f(a^(2^(e-1))) = 1`;
  - factors out `ker f`.
  Every step keeps `a^(2^(e-1)) != 1`. At the end `Omega_1(Z(Q))` is cyclic, so the unique minimal
  normal subgroup is `<a^(2^(e-1))>` and `Q` has a faithful irreducible character.
- `run2`/`run3` record sizes and order profiles; `mono2.g` is an earlier random-pick variant.
- `run6` computes `Irr` of the smallest model found and lists the degrees of the faithful
  irreducible characters: `[8]` at `e = 3` (order `2^8`) and `[32]` at `e = 4` (order `2^14`).
- `perm.g`/`run4`/`run5` grow a large subgroup `H` avoiding the socle generator. `H` is then
  core-free (a normal subgroup meeting nothing but 1 of the cyclic socle is trivial), and the code
  reports `[Q : H]` and the cycle types. Degrees are 32 at `e = 3` and 256 at `e = 4`, with `a`
  semiregular in both. At `e = 5`, `FactorCosetAction` exceeds the 1.5 GB limit, and `run5` records
  indices `2^42` and `2^46`.
- All runs are randomized. The numbers are upper bounds on the minimal model, not minima.
