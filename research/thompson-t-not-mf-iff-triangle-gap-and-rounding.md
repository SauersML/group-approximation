---
rg: 2
id: thompson-t-not-mf-iff-triangle-gap-and-rounding
kind: claim
title: "Thompson's T is not MF iff two independent necessary conditions hold through the triangle cover Delta(4,3,5) -> T: a relator gap on genuine representations of Delta, and a uniform, doubled, trivially padded rounding of T-near pairs onto genuine representations of Delta; gamma_2 = (sqrt 5 - 1)/2"
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the one-gap criterion over the free product Z/4 * Z/3, where rounding to exact representations is automatic; this inserts the linear, residually finite cocompact Fuchsian group Delta(4,3,5) between Z/4 * Z/3 and T and splits that single gap into a statement about honest representations of Delta and a uniform stability statement for Delta, each necessary and neither sufficient alone.
  thompson-t-pentagon-winding-sandwich: that extracts the integer invariant kappa_P and proves T not MF ==> (PW); this shows that the undoubled form of the rounding half already implies (PW), so kappa_P is exactly the obstruction that the doubling in the rounding half is there to kill.
  thompson-t-pentagon-winding-rigidity: that is the open necessary condition (PW); the two halves here are finer, since (PW) follows from the undoubled rounding statement but not from either half as stated.
  lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice: that realises T-bar as a quotient of a Brieskorn lattice to transport central projections; this uses the triangle quotient Delta(4,3,5) of T's presentation only to split the MF question, and never lifts to T-bar.
  simple-kazhdan-mf-lives-in-gap-near-representations: that shows perturbative arguments at genuine representations are free for rationally perfect groups; this moves the genuine representations to a cover (Delta) that has many of them, so the perturbative half becomes a real statement (the rounding half) about Delta rather than about T.
  torus-knot-groups-are-rq-stable: that is Willett's R_q-padded stability for the torus knot group K(3,4), a cover of Z/4 * Z/3; this needs rounding onto the smaller cover Delta(4,3,5) with padding only by trivial blocks, which is exactly the form Willett's Theorem 1.10 does not give.
artifacts:
  - experiments/thompson-t-triangle-cover-2026-09-17/gamma2.py
  - experiments/thompson-t-triangle-cover-2026-09-17/out_gamma2.json
---

**ESTABLISHED** by `thompson-t-not-mf-iff-triangle-gap-and-rounding-proof` (written proof, with an exact
computation of `gamma_2`).

## Setting

The notation is that of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`. Exact pairs `(A,B)` satisfy
`A^4 = B^3 = 1`. `D(A,B)` is the maximum operator-norm defect of `r_1`, `r_2` and `r_P = (ba)^5`. A
**delta-pair** is an exact pair with `D < delta`. `L = 34` is the length of `r_2`, the longest relator.

Put `Delta = Delta(4,3,5) = <a, b | a^4, b^3, (ba)^5>`. It is perfect, a cocompact Fuchsian group, and
`T = Delta / <<r_1, r_2>>`. A **genuine** pair is a unitary representation of `Delta`, that is, an exact pair
with `(BA)^5 = 1`. Put `d_T(A,B) = max(||r_1(A,B) - 1||, ||r_2(A,B) - 1||)`. Define

```text
gamma_n = min { d_T(rho) : rho a nontrivial genuine pair in U(n) }      (gamma_n = +infinity if there is none),
```

and the two conditions:

> **(R_Delta)**, `thompson-t-triangle-genuine-rep-relator-gap`: `inf_n gamma_n > 0`.
>
> **(S_T)**, `thompson-t-near-pairs-round-to-triangle-reps`: for every `eps > 0` there is `delta > 0` such
> that for every delta-pair `phi = (A,B)` in `U(n)` there are `k >= 0` and a genuine pair `rho` in
> `U(2n+k)` with `||rho(s) - (phi (+) phi-bar (+) 1_k)(s)|| < eps` for `s = a, b`.

## Statement

1. **(Equivalence.)** `T` is not MF  <=>  (R_Delta) and (S_T).
2. **(Each half is necessary on its own, and neither can be dropped.)**
   - not (R_Delta) ==> `T` is MF;
   - not (S_T) ==> `T` is MF.

   So the target splits into two statements, and each of them can fail independently of how the other one
   is settled. Neither implies the target alone.
   - (R_Delta) is a statement about honest representations of a linear group.
   - (S_T) is a uniform stability statement. In each fixed dimension it is automatic, with `delta = delta_n`,
     so its whole content is uniformity in `n`.
3. **(General form.)** The same holds for every finitely presented intermediate quotient
   `Z/4 * Z/3 ->> Gamma ->> T` in which `a, b` map to `a, b`. It holds with `(R_Gamma)`, the gap of `D` on
   nontrivial genuine `Gamma`-pairs (on genuine `Delta`-pairs `D = d_T`), and `(S_T^Gamma)`, the doubled and trivially padded rounding onto
   genuine `Gamma`-pairs.
   - For `Gamma = Z/4 * Z/3`, `(S)` is automatic and `(R)` is the w16 criterion.
   - For `Gamma = T`, `(R)` is vacuous (`gamma = infinity`, by Malcev) and `(S)` is the target.
   - `Delta(4,3,5)` is the first intermediate quotient that is linear and residually finite. It is the
     natural place to split the target.
4. **(Undoubled rounding implies PW.)** Suppose the variant of (S_T) without the conjugate summand holds:
   `phi (+) 1_k` is eps-close to a genuine pair. Then (PW) holds, that is, every delta-pair has
   `kappa_P = 0` for small delta. More generally, (PW) follows from this variant with the trivial block
   replaced by any genuine pair. So the summand `phi-bar` in (S_T) is exactly the device that removes the
   pentagon winding, in the sense of item 6 of `thompson-t-pentagon-winding-sandwich`, and (S_T) cannot be
   strengthened to the undoubled form without first proving (PW).
5. **(Facts about `gamma_n`.)**
   - `gamma_n` is attained when finite, and it is positive.
   - `gamma_(n+1) <= gamma_n`.
   - `gamma_n` is the minimum of `d_T` over nontrivial irreducible genuine pairs of dimension `<= n`.
   - `delta_n <= gamma_n`.
   - `gamma_1 = infinity`, since `Delta` is perfect.
6. **(Exact value `gamma_2 = 2 sin(pi/10) = (sqrt 5 - 1)/2 = 0.6180339887...`.)**
   - The nontrivial genuine pairs in `U(2)` are, up to conjugacy, exactly the two binary-icosahedral
     representations into `SU(2)`: `tr A = 0`, `tr B = -1`, `tr BA = 2 cos(2 pi k/5)`, `k = 1, 2`.
   - In both, `r_1 = 1` exactly.
   - `||r_2 - 1||` is `2 cos(pi/5) = 1.618...` for `k = 1` and `2 sin(pi/10) = 0.618...` for `k = 2`.

   So `gamma_2 > delta_1 = 0.5176 > delta_2 = 0.3491`, where `delta_2` is the w17 census value. In
   dimensions 1 and 2 the smallest-defect nontrivial pairs are therefore *not* genuine `Delta`-pairs. The
   pentagon relator carries the whole defect there, which is why (S_T) cannot be dropped.

## Why it matters

- **A decomposition into two prerequisites that can each fail.** A proof that `T` is not MF must prove
  (R_Delta) and (S_T). A proof that `T` is MF may refute either one.
  - (R_Delta) lives entirely in the representation varieties of `Delta(4,3,5)`. `Delta` is a
    finitely generated linear group, hence residually finite, so it has many honest representations. The question is
    whether two fixed words can be almost trivial in a nontrivial honest representation.
  - (S_T) is the operator-norm stability of `Delta` on the doubled pairs. It is implied by the T-free
    statement (S_Delta) recorded in `thompson-t-near-pairs-round-to-triangle-reps`.
- **Where known stability theory must enter.** `thompson-t-padded-cover-stability-is-inert` shows that
  padding by a nontrivial auxiliary block (Willett's `R` and `R_q` stability) transfers nothing to
  (R_Delta). So a stability input has to take the trivially padded form of (S_T).
