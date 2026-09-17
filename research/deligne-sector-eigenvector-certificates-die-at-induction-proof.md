---
rg: 2
id: deligne-sector-eigenvector-certificates-die-at-induction-proof
kind: route
title: Ultralimit eigenvalues are characters, and inducing a character with z -> omega supplies the forbidden eigenvector
target: deligne-sector-eigenvector-certificates-die-at-induction
requires: [deligne-multiplier-trivial-on-sl2xsl2-and-parabolics]
---

Notation of the target.  All norms are operator norms.

**Step 0 (corona homomorphism).**  Fix a sector model `sigma_n`, pass to the
subsequence in (V1), and fix a free ultrafilter `U` on it.  Put
`M = prod_n M_(d_n)` and `J = {(x_n) : lim_U ||x_n|| = 0}`.  Then
`g -> [sigma_n(g)]` is a homomorphism `E_3 -> U(M/J)`, since the defects tend
to zero along `U`.  It sends `z` to `omega`.  By the universal property of
`C*(E_3)` it induces a unital `*`-homomorphism `pi : A_omega -> M/J` with
`pi(u_g) = [sigma_n(g)]`.

**Step 1 (limits are characters).**  Let `xi_n` and `lambda_n` be as in (V1),
and put `lambda(k) = lim_U lambda_n(k)`.  Then `|lambda_n(k)| -> 1`, because
`sigma_n(k)` is unitary.  For `k, k' in K`, write `o(1)` for vectors whose
norm tends to zero along `U`:

    sigma_n(kk') xi_n = sigma_n(k) sigma_n(k') xi_n + o(1)
                      = lambda_n(k') sigma_n(k) xi_n + o(1)
                      = lambda_n(k) lambda_n(k') xi_n + o(1).

Comparing with `sigma_n(kk') xi_n = lambda_n(kk') xi_n + o(1)` and using
`||xi_n|| = 1` gives `lambda(kk') = lambda(k) lambda(k')`.  Also
`lambda_n(z) xi_n = sigma_n(z) xi_n + o(1) = omega xi_n + o(1)`, so
`lambda(z) = omega`.  The functional `x -> lim_U <x_n xi_n, xi_n>` on `M`
vanishes on `J`.  So it is a state `psi` of `M/J`, and `phi = psi o pi` is a
state of `A_omega`.  It satisfies
`phi(u_k) = lim_U <sigma_n(k) xi_n, xi_n> = lim_U lambda_n(k) = lambda(k)`.

**Step 2 (circular branch).**  If `K` has no character with `z -> omega`,
Step 1 shows that no sector model has asymptotic eigenlines for `K`.  If
sector models exist, (V1) is therefore false.  If none exist, (V1) holds
vacuously.  So (V1) is equivalent to emptiness.

**Step 3 (refuted branch).**  Let `chi : K -> T` be a character with
`chi(z) = omega`.  Let `H_chi` be the space of functions `f : E_3 -> C` with
`f(gk) = conj(chi(k)) f(g)` for `k in K` and `sum_(gK) |f(g)|^2 < inf`,
with `(g' . f)(g) = f(g'^(-1) g)`.  This is a unitary representation of
`E_3`.

- Since `z` is central, `(z . f)(g) = f(z^(-1) g) = f(g z^(-1))
  = conj(chi(z^(-1))) f(g) = omega f(g)`.  So the representation factors
  through `A_omega`.
- Let `f_0(k) = conj(chi(k))` for `k in K` and `f_0 = 0` off `K`.  It is well
  defined because `chi` is a character, and it has norm one.  For `k' in K`,
  `(k' . f_0)(g) = f_0(k'^(-1) g)` is supported on `K`.  For `g in K` its
  value is `conj(chi(k'^(-1) g)) = chi(k') conj(chi(g))`.  So
  `k' . f_0 = chi(k') f_0`.

The vector state of `f_0` is a state `phi` of `A_omega` with
`phi(u_k) = chi(k)` for all `k in K`, so (V2) fails for `(K, chi)`.  If
`q in A_omega` projects onto the `chi`-eigenspace of `K` in every
representation, then it acts as the identity on `f_0 != 0`.  Hence `q != 0`,
and (V2c) fails.

**Step 4 (application).**  The claim
`deligne-multiplier-trivial-on-sl2xsl2-and-parabolics` supplies a
homomorphism `phi_H : p^(-1)(H) -> T` with `phi_H(z) = omega` for
`H in {SL_2(Z) x SL_2(Z), P_S(Z), P_K(Z)}`.  Restrictions to `p^(-1)(H')`,
for `H' <= H`, keep `z -> omega`, so Step 3 applies.  Steps 2 and 3 are
exhaustive, because a character with `z -> omega` either exists on `K` or
does not.  ∎

**Remark (what the proof uses).**  Only the universal property, one
ultralimit and one induced representation.  No property (T), no
congruence-subgroup input and no genus assumption are used.  The same proof
works for every finite central extension `1 -> C -> E -> G -> 1` and
every nontrivial character of `C`.
