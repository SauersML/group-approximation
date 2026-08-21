---
rg: 2
id: kazhdan-subgroup-weak-ucp-exactifies-microstates
kind: claim
title: A weakly ucp-stable Kazhdan subgroup lets HNN and coset-wreath microstates be taken exact on it
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that applies the Kazhdan averaging to the whole group and concludes weak ucp-stability equals flexible stability on hyperlinear approximations; this applies it only to a Kazhdan subgroup C of an unstable host and obtains exactness on C alone, the relative form.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that consumes flexible HS-stability of the HOST A and finishes the non-hyperlinearity proof; this consumes weak ucp-stability of the SUBGROUP C only and does not finish anything — it exactifies the microstates on C and leaves the Lambda-exact face of the collapse as the whole remaining problem.
  subgroup-exact-outliers-do-not-exist: that corrects almost-representations of SL_3(Z) that are ALREADY exact on a finite-index subgroup; this produces exactness on the Kazhdan subgroup from a named stability hypothesis (weak ucp-stability) and applies to any pair C <= A, as a preprocessing step for HNN or wreath microstates.
  no-published-unconditional-codense-stable-host: that records that weak ucp-stability of the HOST cannot be consumed by the HNN mechanism because infinite-dimensional dilations resurrect l^2(A/C); this agrees (the leak survives) and shows that weak ucp-stability of the SUBGROUP is consumable exactly as far as the C-exact face.
  sl3z-regular-microstates-are-congruence-correctable: that hole asks for an UNCONDITIONAL correction of regular microstates of the lattice to congruence representations; this derives such a correction for the lattice restriction of HNN/wreath microstates from the stability hypothesis sl3-z-weakly-ucp-stable.
---

**Data.**  `C` a finitely generated group with Kazhdan's property (T),
Kazhdan pair `(S, kappa)` with `S = S^(-1)` finite generating; `A` any
countable group containing `C` as a proper subgroup; `a_1 in A - C`.  Two
marked groups:

```text
G = < A, t | t c t^(-1) = c  (c in C) >,                          (WE1)
W = (direct_sum_(A/C) C_2) rtimes A,  e = the lamp at the coset C. (WE2)
```

Hyperlinear approximation (Dogon arXiv:2211.10492 Def 1.4): maps
`phi_n : G -> U(d_n)` with `|| phi_n(g) phi_n(h) - phi_n(gh) ||_2 -> 0`
for all `g, h` and `liminf || phi_n(g) - 1 ||_2 >= sqrt 2` for `g != e`,
where `|| . ||_2` is the normalized Hilbert--Schmidt norm.  `C` is
**weakly ucp-stable** (Dogon Def 1.5) if every hyperlinear approximation
`psi_n : C -> U(H_n)` is pointwise asymptotic to compressions
`P_n pi_n(.) P_n` of genuine unitary representations
`pi_n : C -> U(H^_n)` on possibly INFINITE-dimensional Hilbert spaces
`H^_n` containing `H_n`, `P_n` the projection onto `H_n`.  Flexible
HS-stability implies weak ucp-stability; the converse fails (Dogon p. 4:
any group whose full C*-algebra has Kirchberg's LLP is weakly ucp-stable,
so every amenable group is, while non-residually-finite amenable groups are
not flexibly HS-stable).

**THEOREM.**  Assume `C` has property (T) and is weakly ucp-stable.  Let
`phi_n : G -> U(d_n)` be a hyperlinear approximation of `G` (resp. of
`W`).  Then there are dimensions `d'_n` with `d'_n / d_n -> 1`, partial
isometries `W_n : C^(d_n) -> C^(d'_n)` with
`|| W_n^* W_n - 1 ||_(2,d_n) -> 0` and `|| W_n W_n^* - 1 ||_(2,d'_n) -> 0`,
and a hyperlinear approximation `phi'_n : G -> U(d'_n)` (resp. of `W`)
such that

```text
(i)   phi'_n restricted to C is a GENUINE unitary representation of C;
(ii)  phi'_n(t) commutes EXACTLY with phi'_n(C)
      (resp. phi'_n(e) is a symmetry commuting exactly with phi'_n(C));
(iii) || phi'_n(g) - W_n phi_n(g) W_n^* ||_(2,d'_n) -> 0 for every g,
      in particular tr phi'_n(g) -> delta_e(g).                   (WE3)
```

Consequently, in the matrix ultraproduct `M = prod_U M_(d'_n)` the
representation `pi = [phi'_n|_A]` of `A` has regular trace, its
restriction to `C` is an ultraproduct of genuine finite-dimensional
representations of `C`, and `k = [phi'_n(t)]` (resp. the lamp) lies in
`pi(C)' cap M` by exact finite-level commutation, while `[k, pi(a_1)]` has
trace `0` by Britton (`[t, a_1] != e` in `G`; the wreath analogue is
`(e . a_1 e a_1^(-1)) != e`).  So `k` is a witness AGAINST the relative
commutant collapse `pi(C)' cap M = pi(A)' cap M` living on the **C-exact
face** of that collapse.

**What this does and does not do.**  It moves the stability hypothesis
from the host `A` to the subgroup `C` and from flexible HS-stability to
weak ucp-stability, at the price of proving nothing by itself: the
Stinespring dilation is a representation of `C`, not of `A`, so the
quasi-regular leak `l^2(A/C)` (the lamp of the coset Bernoulli wreath)
survives the correction untouched, exactly as
`no-published-unconditional-codense-stable-host` records for host-side weak
ucp-stability.  What is gained is that the enemy is confined to the
`C`-exact face, where the arithmetic lanes already have partial closures
(`odd-congruence-lambda-exact-sector-collapses`,
`lambda-exact-face-of-the-collapse-closes`) and one open full-face claim
(`lambda-exact-face-closes-at-p-three`).

**Superseded for `C = SL_n(Z)` (2026-08-21).**  The same averaging applied
to `C` alone proves `kazhdan-weak-ucp-stability-is-flexible-stability`:
for a Kazhdan group, weak ucp-stability IS flexible HS-stability on
hyperlinear approximations.  When `C` itself carries a thin co-dense
`(tau)` pair (`sln-z-thin-codense-tau-pair`, `n >= 3`), the HNN theorem
over that pair consumes the very same hypothesis `sl3-z-weakly-ucp-stable`
and reaches the goal with no face closure
(`non-hyperlinear-from-sl3-z-weak-ucp-stability`); the face-confinement
route this theorem offered for the p = 3 pair was therefore retired as
dominated.  The theorem keeps its value for Kazhdan subgroups `C` that
are stable on hyperlinear approximations but have NO known thin co-dense
`(tau)` pair inside them, and for the coset-wreath endpoint, where the
lamp rather than a new letter is exactified.

**Why full (T) and not (T;FD).**  The first correction step applies a
Kazhdan pair to the conjugation representation `Ad pi_n` of `C` on the
Hilbert--Schmidt operators of the possibly infinite-dimensional dilation
space `H^_n`; (T;FD) sees only finite-dimensional representations and does
not reach it.  The second step (the letter) runs in `B(V_n)`, finite
dimensional, where (T;FD) would suffice.  So the theorem covers
`C = SL_n(Z)` (`n >= 3`) and Kazhdan lattices in general, but not
`C = SL_2(Z)` of the Dogon--Vigdorovich pair.
