---
rg: 2
id: tracial-to-uniform-lifting-for-sl-n-z
kind: claim
title: Every representation of SL_N(Z) into a tracial matrix ultraproduct lifts to the operator-norm ultraproduct, up to a vanishing corner
distinct_from:
  sln-z-flexibly-hs-stable: that is the stability statement about almost-representations; this is the equivalent LIFTING statement about exact representations into the tracial quotient, which isolates the norm gap as a single lifting problem and makes Ulam stability (known) do the rest.
  bounded-degree-two-primitives-for-higher-rank-lattices: that tried to run a normalized Newton iteration and was found to need operator-small defects anyway; this is the honest residue -- producing operator-small defects from trace-small ones -- with no cohomological machinery presupposed.
---

Let `A = prod_U^(op) M_(d_m)` be the operator-norm ultraproduct of
matrix algebras, `I` its ideal of 2-null sequences, and
`M = A / I` the tracial matrix ultraproduct.  Claim: for `N >= 3`
every unitary representation `pi : SL_N(Z) -> U(M)` admits a
projection `Q in M` of trace `1` (i.e. `1 - Q` of trace zero, a
vanishing corner) and a unitary representation
`tilde pi : SL_N(Z) -> U(Q A Q)` with `tilde pi(g) + I = pi(g) Q`
for all `g`.  (Flexible form; the strict form asks `Q = 1`.)

Equivalently, in sequence language: every sequence `sigma_m` with
normalized-HS defect `-> 0` is 2-close to a sequence `sigma'_m` with
OPERATOR-norm defect `-> 0` (after cutting corners of vanishing
trace).

## Attempts

- **Why this is the whole norm gap.**  By Burger--Ozawa--Thom
  (`SL_n(Z)`, `n >= 3`, uniformly stable in operator norm) and
  Glebsky--Lubotzky--Monod--Rangarajan [arXiv:2301.00476] (most
  high-rank lattices, all submultiplicative norms), operator-small
  defects are operator-close to exact representations.  Hence this
  claim IMPLIES flexible HS-stability of `SL_N(Z)`, `N >= 3`, and
  conversely HS-stability implies the claim (an exact nearby
  sequence has zero defect and lifts trivially).  So for Ulam-stable
  groups:  HS-stable  <=>  tracial-to-uniform lifting.  The
  normalized Hilbert--Schmidt norm is not submultiplicative, which
  is exactly why the uniform-stability theorems stop short of it.
- **What lifting technology exists, and why it falls short.**
  Ucp lifts through `A -> A/I` exist when `C^*(Gamma)` has the
  lifting property, but a ucp lift's multiplicativity defect lies in
  `I` -- trace-small, not operator-small -- so ucp lifting does not
  touch the problem.  The lane's own "(T)-lifting" technology lifts
  CENTRAL elements (Kazhdan projections applied to almost-invariant
  vectors) with operator control, because invariant vectors of the
  genuine ultraproduct action are 2-limits of averages of
  operator-bounded orbit points; the representation itself has no
  such averaging formula.  Bounded generation by root subgroups
  (Carter--Keller) reduces the lift to finitely many root
  unitaries, each of which lifts trivially (`Z` is free), with the
  Steinberg relations as the obstruction -- the same obstruction in
  different clothes.
- **Falsification gate.**  A representation of `SL_N(Z)` into a
  tracial ultraproduct with no operator-norm lift, even after
  cutting a vanishing corner, would refute this claim and (by the
  equivalence) give a non-HS-stable higher-rank lattice via a
  mechanism unrelated to the central-extension obstructions of
  Ioana--Spaas--Wiersma -- a result of independent interest.  The
  known obstructions to lifting (ISW) live in `H^2(Gamma; R)`, which
  vanishes here.
- **The absorber lemma and the exact form of the problem
  (2026-08-21).**  Let `A` be the operator-norm ultraproduct, `I`
  the trace-null ideal, `sigma : F_S -> U(A)` the word-extension of
  generator lifts of `pi`, and `c_w = sigma(w) - 1 in I` for `w` in
  the normal closure `R` of the relators (countably many).  Arveson's
  theorem gives an approximate unit of `I` quasi-central for the
  countable set `sigma(F_S)`; countable saturation of `A` (with the
  definable trace) turns the net into ONE element: a positive
  contraction `e in I` with `[e, sigma(g)] = 0` for all `g in F_S`
  and `e c_w = c_w = c_w e` for all `w in R`, EXACTLY in `A`.  Hence
  every `sigma(w)`, `w in R`, is the identity on `ker e` (as a
  subspace of the Hilbert-space ultraproduct `H_U`), and
  `K = ker e` has co-trace zero.  The `R`-fixed subspace
  `H_0 = intersection_w ker(sigma(w) - 1)` contains `K`, is
  `sigma(F_S)`-invariant because `R` is normal, and therefore
  carries a GENUINE unitary representation of `Gamma`.  So the
  lifting claim is EXACTLY: `H_0` contains an INTERNAL
  `sigma`-invariant subspace of co-trace zero (an ultraproduct of
  subspaces `L_m subset H_m` with operator-norm almost-invariance
  and exact relators in the limit); given one, the compressions are
  a lift on a vanishing corner.  By saturation this is a finite-
  satisfiability statement: for finitely many generators, relators
  and `eps > 0`, an internal projection `L >= 1_K` with
  `|| [L, sigma(s)] ||_op < eps` and `|| (sigma(w) - 1) L ||_op < eps`.
- **Why the natural candidates fail (the ramp).**  The orbit spans
  `L^(N) = join_(|g| <= N) sigma(g) K` are internal, lie in `H_0`,
  have co-trace zero, and satisfy the relator condition, but
  `sigma(s) L^(N) subset L^(N+1)` with increments that are
  trace-null yet of operator norm one, so `[L^(N), sigma(s)]` is
  never operator-small; filling the rank-tiny holes by arbitrary
  unitaries restores unitarity but leaves relator defects of
  operator norm one on the holes, and the exactly `R`-fixed subspace
  of the modified representation can collapse.  The one-generator
  "ramp" (`e_m = diag(0,...,0, 1/k, ..., 1)`, `sigma = ` cyclic
  shift, `k -> infinity`, `k/d -> 0`) shows the phenomenon with NO
  relators at all: `e` is trace-null and exactly commutes in the
  limit, no level set of `e` is operator-almost-invariant, and yet
  the exact representation exists trivially (all of `H`).  So the
  invariant subspace must be sought away from level sets of the
  absorber -- the content is genuinely global, and this is the
  cleanest known statement of what separates normalized from
  operator-norm stability.
