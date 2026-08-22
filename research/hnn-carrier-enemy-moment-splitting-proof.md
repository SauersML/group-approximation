---
rg: 2
id: hnn-carrier-enemy-moment-splitting-proof
kind: route
title: Relative icc pins the conditional expectations and commutation factorizes the trace
target: hnn-carrier-enemy-moment-splitting
requires:
  - hecke-averaging-realizes-commutant-expectation
---

Throughout, `E_(L(Gamma)) : N -> L(Gamma)` is the trace-preserving
conditional expectation (it exists for any von Neumann subalgebra of
a finite algebra), and we use the relative-icc fact recorded in
`relative-commutant-collapse-for-sl2-pair`: every nontrivial element
of `Gamma = SL_n(Z[1/p])` (non-central, automatic for `n` odd) has
INFINITE-INDEX centralizer in `Lambda = SL_n(Z)` (Borel density,
`arithmetic-pair-ultrapower-no-leak-proof` Step 2; the earlier "finite
centralizer" was false, corrected 2026-08-21), hence infinite
`Lambda`-conjugacy class, so an
element of `L(Gamma)` commuting with `pi(Lambda)` has Fourier
coefficients constant on infinite classes and `l^2`-summable, forcing

```text
L(Lambda)' cap L(Gamma) = C 1                                   (MSP1)
```

(for even `n`, the span of the finite center; `n` odd here).

**Part 1.**  Each `k^m` commutes with `pi(Lambda)` (the relation
`[t, Lambda] = 1` holds in `H`).  For a unitary `u in pi(Lambda)`,
`u E_(L(Gamma))(k^m) u^* = E_(L(Gamma))(u k^m u^*) = E_(L(Gamma))(k^m)`
by `L(Gamma)`-bimodularity, so `E_(L(Gamma))(k^m) in L(Lambda)' cap
L(Gamma) = C 1`; evaluating the trace gives `E_(L(Gamma))(k^m) =
tau(t^m) 1`.  Hence for `gamma in Gamma`,

```text
tau(gamma t^m) = tau( pi(gamma) E_(L(Gamma))(k^m) )
             = tau(t^m) tau(pi(gamma)) = tau(t^m) delta_e(gamma),
```

which is `(MS1)`.  A word with exactly one `t`-block is conjugate to
`gamma t^m`, and traces are conjugation invariant, so its value is
forced by `(MS1)`; on `Lambda x <t>` this reads `tau(lambda t^m) =
delta_e(lambda) hat(mu)(m)` with `mu` the spectral measure of `k`
(the law of `k` in `(N, tau)` restricted to the abelian
`W*(k)`), i.e. `tau|_(Lambda x <t>) = delta_e otimes hat(mu)`.

**Part 2.**  Let `q in Q`.  Then `q` commutes with all of
`pi(Gamma)`, so by the same bimodularity argument
`E_(L(Gamma))(q) in L(Gamma)' cap L(Gamma) = Z(L(Gamma)) = C 1`,
giving `E_(L(Gamma))(q) = tau(q) 1`.  For `x_1, ..., x_r in
L(Gamma)` and `q_1, ..., q_r in Q`, commute the `q_i` to the right
and use that `Q` is an algebra:

```text
tau(x_1 q_1 ... x_r q_r) = tau( (x_1 ... x_r)(q_1 ... q_r) )
 = tau( x_1 ... x_r E_(L(Gamma))(q_1 ... q_r) )
 = tau(x_1 ... x_r) tau(q_1 ... q_r).
```

Two commuting von Neumann subalgebras whose mixed traces factorize
generate a copy of their von Neumann tensor product with the product
trace (the map `x otimes q -> xq` is a trace-preserving
*-homomorphism on the algebraic tensor product, hence extends), which
is `(MS2)`.  If `tau` is factorial and `Q = C`, irreducibility of
`L(Gamma) subseteq N` is the definition unwound.

**Part 3.**  `(N, tau)` is a tracial von Neumann algebra and
`pi_tau|_Gamma` a unitary representation; `k^m` is a
`pi(Lambda)`-central unitary.  This is exactly the hypothesis set of
`hecke-averaging-realizes-commutant-expectation` with `M = N`, whose
conclusion is `E_Q(k^m) = lim_N S^N(k^m)` with the geometric rate
`delta_0(n, p)` (the expectation there is onto `pi(Gamma)' cap M =
Q`), and `s_m = || E_Q(k^m) ||_2^2` is the corresponding leak scalar
of the far-defect formula.

**Part 4.**  If `k in Q` then `k` commutes with `pi(Gamma)` and
`tau(t^(-1) gamma^(-1) t gamma) = tau(1) = 1` for all `gamma`, which
is `(FC1)`; conversely `(FC1)` for all `gamma` gives, by the
Cauchy--Schwarz equality of unit vectors in `L^2(N)`,
`k pi(gamma) = pi(gamma) k`, i.e. `k in Q`.  Words with no `t` are
pinned by `tau|_Gamma = delta_e`; words with one block by Part 1.
For `mu` Haar, `hat(mu)(m) = delta_(m=0)`, which are exactly the
zero- and one-block values of the canonical trace `delta_e^H`
(Britton normal form: a one-block word `gamma t^m` with `m != 0` is
nontrivial in `H`, and `delta_e^H` vanishes on it; for `m = 0` both
sides are `delta_e`).  The displayed leak coefficient is the trace of
`t^(-1) gamma^(-1) t gamma`, a two-block word.  Finally `k^m -
tau(k^m) 1 perp L^2(L(Gamma))` restates `E_(L(Gamma))(k^m) =
tau(k^m) 1`.
