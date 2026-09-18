---
rg: 2
id: fpbs-zero-entropy-ray-codes-are-support-rigid
kind: claim
title: Pointwise match rigidity holds for the ray code of every zero-entropy ergodic Z-system, so every nonatomic class carried by those rays, of every Krieger type, has totally dissipative diagonal and is no BB boundary class; the rigidity uses only that the future and the past of the coding each determine the point, and it fails at the first step for positive-entropy codes
distinct_from:
  fpbs-rotation-boundary-class-refutes-shadow-summability: that proves pointwise match rigidity for the one ray code built from an irrational rotation and the sign function, using the circle geometry (density of t alpha and the inversion symmetry s(-x) = -s(x)); this proves it for the ray code of an arbitrary aperiodic Borel system whose binary coding is injective on forward and on backward itineraries, which by Krieger's generator theorem covers every ergodic zero-entropy measure-preserving Z-system, and it isolates two-sided injectivity as the exact property used.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills classes dominating a Dini measure through the size of the measure (a first-moment count on the Radon--Nikodym fibre); this kills classes carried by zero-entropy ray sets through the Borel support alone, with no condition on the size or the quasi-invariance of the measure.
---

**ESTABLISHED (written proof; see `research/fpbs-zero-entropy-ray-codes-are-support-rigid-proof.md`).
Theorems 1 and 2 are self-contained given the free-group combinatorics of
`fpbs-rotation-boundary-class-refutes-shadow-summability` (Lemma 4.1, Theorem 3). Theorem 3 imports Krieger's
finite generator theorem and the Pinsker formula `h(T,P) = H(P | P^-)`. Theorem 4 imports the
Dougherty--Jackson--Kechris classification of hyperfinite Borel relations and the Araki--Woods/Krieger type
computations. The extension to hyperbolic groups is Theorem C of `fpbs-rotation-support-rigidity-kills-type-iii-classes`,
which uses the ray code only through the properties proved here.**

**Why this matters for the flagship.** A Bevilacqua--Bowen (BB) certificate for fixed price needs an amenable ergodic
imp action that is partially doubly recurrent (PDR). So its boundary class must *not* be killed. Two kill mechanisms
were known:
- the Dini count, which kills classes that are too *large*;
- rotation match rigidity, which kills one family of *thin* classes.

This result replaces the rotation by an arbitrary zero-entropy system. So the thin side of the dichotomy is governed
by one invariant, the entropy of the coding. The survivors must be both Dini-singular and of positive coding entropy.

**Setting.** `F = <a,b>`; `t_n = a` for odd `n` and `b` for even `n`. Let `(X_0, T)` be an aperiodic Borel automorphism
of a standard Borel space with a Borel `s : X_0 -> {±1}`. On `Omega = X_0 x Z/2` put `sigma(x,j) = (Tx, j+1)` and
`zeta_n(x,j) = t_{n+j}^{s(T^n x)}`. The ray code is `zeta^+(omega) = zeta_1 zeta_2 ...` in `dF`, and `B = zeta^+(Omega)`.
The two itineraries are

`iota_+(x) = (s(T^n x))_{n >= 1}` and `iota_-(x) = (s(T^{-n} x))_{n >= 0}`.

Call `(X_0, T, s)` **two-sided injective** if both `iota_+` and `iota_-` are injective on `X_0`.

**Theorem 1 (pointwise match rigidity).** Let `(X_0,T,s)` be two-sided injective. There is a Borel relation
`Bad ⊂ Omega^2` with countable sections, invariant under `sigma` in each coordinate separately, such that for
`(omega, omega') ∉ Bad` and all `u, v ∈ F`, only finitely many `(k,k') ∈ Z^2` satisfy
`gamma_k(omega) = u gamma_{k'}(omega') v`. Consequently, for every finite `H ⊂ F`, a pair of rays off the null set
`N = ⋃ (h x h')(zeta^+ x zeta^+)(Bad)` has only finitely many `g` with `g eta, g eta' ∈ H B`.

**Theorem 2 (every class on the rays dies).** Let `(X_0,T,s)` be two-sided injective. Let `(Z, mu_Z)` be an imp
`F`-space with a measurable equivariant `xi : Z -> dF` such that `xi_*(mu_Z|_E)` is nonatomic and carried by `F B` for
every `E` of finite measure. Then `F` acts totally dissipatively on `(Z x Z, mu_Z x mu_Z)`. In particular, if `Z` is
ergodic, it is not PDR.

**Theorem 3 (zero entropy suffices).** Let `(X, T, m)` be an ergodic, aperiodic, probability-preserving system with
`h(T) = 0`. Then there are a binary `s` and a `T`-invariant `m`-conull Borel `X_0` on which `(X_0, T, s)` is
two-sided injective.

**Theorem 4 (all Krieger types, for every zero-entropy system).** In the situation of Theorem 3, for every
`lambda ∈ [0,1]` there is a nonatomic, ergodic, `sigma`-quasi-invariant `rho_lambda` on `Omega_0 ⊂ X_0 x Z/2` such
that `nu = sum_g c_g g_* zeta^+_* rho_lambda` is an ergodic `F`-quasi-invariant class of type `III_lambda`. Its Maharam
extension and every imp action over it have totally dissipative diagonal.

**Calibration.**
- *Rotation.* The rotation code of the previous node is two-sided injective on its `Omega_0` (its Lemmas 1.1(2) and
  5.1). Theorem 1 then reproduces its Proposition 5.2 with a relation `Bad` that contains the old one.
- *`F_2` has cost 2,* so no BB certificate may exist. The theorems only remove candidates.
- *Positive entropy (where it dies).* Take `X_0 = {±1}^Z` with the Bernoulli shift and `s(x) = x_0`. Then
  `B` is the set of all type-alternating rays. For any two rays `z, z'` of `B` that begin with an `a`-letter, every
  alternating word `w` of even length ending in a `b`-letter gives `w z, w z' ∈ B`. So *every* pair has infinitely
  many joint returns, and Theorem 1 fails for all pairs. The failure is at Lemma 4.1 of the previous node, whose
  uniqueness needs the future to determine the past. More generally, `h(T) > 0` forces
  `H(P | P^+) > 0` for every generating partition, so forward injectivity fails on every conull set. Hence the
  support method stops exactly at positive entropy. This is a statement about the method: it does not say that
  positive-entropy classes survive.

**Named open statement left.** *Positive-entropy thin classes.* Let `(X,T,m)` have positive entropy with a binary
coding, and let `rho` be Dini-singular, i.e. not caught by the Dini count. Is the diagonal over `nu_rho`, or over its
Maharam extension, totally dissipative? A positive answer, together with this result and the Dini theorem, would
cover every class carried by type-alternating ray sets. The surviving candidates for BB certificates would then have
to live on rays that are not coded by any stationary process.
