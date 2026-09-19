---
rg: 2
id: even-degree-localizing-hankel-attains-truncated-moment-optimum
kind: claim
title: For an even truncation the localizing-Hankel threshold is the exact minimum of sup supp over positive measures with the given moments
distinct_from:
  thompson-f-32-term-cogrowth-bound-is-the-moment-optimum: that is the F-specific statement that the 32 published cogrowth terms certify 0.910677539452 and no more, together with the whole table theta*(N) for N <= 31 and the window exchange rate; this is only the general moment-theoretic step its route leaves unproved, namely that at EVEN N the threshold the script bisects is the optimum and not merely a valid lower bound.
  thompson-f-moment-data-cannot-certify-nonamenability: that says no finite list of exact cogrowth counts can prove ||P|| < 1, an upper-side obstruction about the group; this is a truncated-moment-problem statement with no group in it, about whether an even-degree relaxation is tight.
---

**OPEN** (split out 2026-09-18 as the unproved step of
`thompson-f-32-term-cogrowth-bound-is-the-moment-optimum-proof`, after referee
lens 2 refuted the claim-level assertion that `theta*(N)` is computed exactly
for *every* `N <= 31`. See `## Attempts` there and in
`thompson-f-32-term-cogrowth-bound-is-the-moment-optimum`.)

Fix real numbers `M_0 > 0, M_1, ..., M_N` with `N = 2d` even, and put

    theta*(N) = inf { sup supp nu : nu a positive measure on [0, oo)
                      with integral x^j dnu = M_j for j = 0..N }.

Let `A(theta)` be the `d x d` localizing Hankel matrix
`A(theta)_{ij} = theta M_{i+j+1} - M_{i+j+2}`, `0 <= i, j <= d-1`, the Hankel
matrix of the functional `s -> L(x(theta - x)s)`, and let

    theta_A = inf { theta : A(theta) is positive definite
                            and (M_{i+j})_{i,j<=d} is positive semidefinite }.

**Claim.** `theta*(N) = theta_A`.

The easy half is proved in
`thompson-f-32-term-cogrowth-bound-is-the-moment-optimum-proof` step 6 and is
not at issue: because `x >= 0` on the support, any `nu` with those moments and
`sup supp nu <= theta` makes `L(x(theta - x)s^2) >= 0` for every polynomial `s`,
so `theta*(N) >= theta_A` and every tabulated even-`N` row is a valid lower
bound on `sup supp mu_2`, hence on `||P||^2`. What is open is the converse,
that a representing measure supported in `[0, theta]` actually **exists** as
soon as the two matrices have those signs — i.e. that the even-degree
relaxation is tight and the tabulated value is the *optimum*, not just a bound.

**What the proof would have to supply, and why the obvious citation is not
enough.** The route cites "the classical even-degree Hausdorff condition" with
no author, reference or statement. The hypotheses actually needed differ from
that name:

- the interval is `[0, theta]` with `theta` *moving*, so this is the truncated
  Stieltjes/Hausdorff problem on a variable interval, not the classical
  Hausdorff problem on `[0, 1]`;
- positivity is needed for the Hankel matrix `(M_{i+j})_{i,j<=d}` *jointly*
  with the localizing matrix, not for either alone;
- tightness of the infimum needs closedness of the truncated moment cone over a
  compact interval (Markov-Lukacs / Krein-Nudelman), a reference this
  repository cites elsewhere but which is not cited there.

At **odd** `N = 2d+1` none of this is needed: the route's own steps 2-5 build
the extremal measure explicitly as the spectral measure of the `(d+1)`-square
truncated multiplication operator `J`, which has exactly the prescribed moments
because no truncation occurs below degree `d`. That construction is
self-contained and was verified by all three referees. It is precisely the
"one free extra moment" trick that fails to be available at even `N`, which is
why the even rows need an import.

**Numerical evidence (not a proof).** Referee lens 1 tested the even rows two
independent ways and found no disagreement: a direct grid LP for existence of a
measure on `[0, theta]` at `N = 4, 6, 8, 10` was infeasible `0.0005` below the
tabulated `theta*(N)` and feasible `0.0005` above in every case; and minimising
`lambda_max(J(t))` over the free next moment `M_{2d+1}` subject to `J(t) >= 0`
matched the tabulated `theta*(N)` to `1e-13` at `N = 4` and `1e-10` at
`N = 10, 16`. So the statement is expected to be true; it is the citation that
is missing, not the fact.

## Attempts

- **2026-09-18: cited, not proved (`thompson-f-32-term-cogrowth-bound-is-the-moment-optimum-proof`
  step 6).** The route says only that "optimality at even `N` is the classical
  even-degree Hausdorff condition, which is **not** re-proved here", with no
  author, reference or statement, and the claim node then asserted without
  caveat that `theta*(N)` is computed exactly for every `N <= 31` and that the
  even row `0.901532` at `N = 24` is "optimal at its length". Referee lens 2
  refuted that. Dies on: an unnamed import whose hypotheses do not match the
  name invoked. The repair is either to name and check the theorem (see the
  three bullets above) or to restate every even row as a lower bound only.
