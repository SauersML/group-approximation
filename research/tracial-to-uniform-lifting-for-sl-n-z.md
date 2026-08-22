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
- **Multiplicative versus additive corrections (2026-08-21).**  For
  unitaries, 2-norm errors propagate LINEARLY through words of
  bounded length: `|| u v - u' v' ||_2 <= || u - u' ||_2 + || v -
  v' ||_2`.  Consequently every step of Kazhdan's averaging argument
  for amenable subgroups (`sigma-bar(g) = E_k sigma(g k) sigma(k)^(-1)`
  over Folner sets, then polar correction) transplants verbatim from
  operator norm to normalized HS -- amenable subgroups can be made
  EXACT inside the ideal `I` at 2-cost `O(defect)`, consistent with
  Hadwin--Shulman.  The quadratic-term obstruction of the normalized
  Newton iteration arises ONLY from ADDITIVE corrections
  `(1 + x) sigma`, and that is precisely the form of the gluing step
  in every known Ulam-stability proof for high-rank lattices
  (Burger--Ozawa--Thom: bounded generation by root subgroups plus a
  bounded-cohomology primitive; Glebsky--Lubotzky--Monod--Rangarajan:
  asymptotic-cohomology primitive, defect diminishing).  So the
  residue of this claim is exactly a MULTIPLICATIVE gluing of local
  amenable corrections across the bounded generation of `SL_N(Z)` by
  root subgroups (Carter--Keller) -- a nonabelian replacement for the
  vanishing of bounded `H^2` -- and the abelianized version of that
  gluing is already available (`abelian-lifting-obstruction-
  vanishes-for-sl-n-z`).  Any attack should be designed so that no
  correction is ever added to a unitary; every correction should
  replace a unitary by a nearby unitary.
- **The Reiter obstruction: why (T)-lifting is inherently tracial
  (2026-08-21).**  The Steinberg presentation of `St_n(Z)`, `n >= 3`,
  has all relations inside rank-two root subsystems, so `St_n(Z)` is
  the colimit of NILPOTENT pieces (`Z`, `Z^2`, `H_3(Z)`), each of
  which can be made exact inside `I` multiplicatively (Kazhdan
  averaging, amenable HS-stability); the quotient by `K_2(Z) = Z/2`
  is a finite central adjustment.  Gluing column by column reduces
  to: given an EXACT representation `rho` of `Gamma' = SL_(n-1)(Z)`
  and an almost-equivariant almost-representation of the abelian
  column `V = Z^(n-1)`, produce an exactly `rho`-equivariant exact
  `V`-representation -- equivalently one unitary `u_1 = v(e_1)` that
  commutes EXACTLY (operator norm, internally) with the genuine
  Kazhdan action `Ad rho(Stab(e_1))` and satisfies finitely many
  module relations.  Internal exact invariant elements cannot be
  produced by averaging: an averaging kernel `mu_n` on a group makes
  `Ad rho(mu_n)(u_1)` exactly invariant in operator norm only if
  `|| delta_h mu_n - mu_n ||_(l^1) -> 0`, which is Reiter's
  condition, i.e. AMENABILITY; the Kazhdan projection converges only
  in the `C^*`-norm, which controls 2-norm (tracial) invariance.
  Hence every "(T)-lifting" in this lane (Lambda-central elements
  into the congruence commutant tower, etc.) is a statement in the
  tracial quotient, never in the operator-norm ultraproduct, and the
  column-extension step is blocked by non-amenability at exactly the
  point where the Steinberg induction needs it.  Any proof of this
  claim must therefore produce exact invariant elements WITHOUT
  averaging -- by a global construction (a fixed point of a
  non-averaging map, a spectral-gap-with-gap absorber, or an
  entirely different lift) -- and a disproof would likely come from
  exhibiting an almost-representation whose column data admits no
  internal invariant completion.
- **Correction to the Reiter paragraph: exact internal commutant
  elements DO exist; the residual is joint exactness (2026-08-21).**
  The obstruction above is misattributed.  At every finite level the
  trace-preserving conditional expectation `E_m : M_(d_m) -> rho_m(H)'`
  onto the (finite-dimensional) commutant of a genuine representation
  `rho_m` of a Kazhdan group `H` is the orthogonal projection onto the
  `Ad rho_m(H)`-invariant vectors of `L^2(M_(d_m))`; it is ucp, so
  `|| E_m(u) ||_op <= 1`, and `E_m(u)` commutes with `rho_m(H)` EXACTLY.
  Property (T) gives
  `|| u - E_m(u) ||_2 <= kappa^(-1) max_s || [u, rho_m(s)] ||_2`, and
  polar-correcting inside the finite von Neumann algebra `rho_m(H)'`
  (partial isometries extend to unitaries there) yields a unitary
  `u'_m in rho_m(H)'` with
  `|| u - u'_m ||_2 <= 3 kappa^(-1) max_s || [u, rho_m(s)] ||_2`
  (`|| E(u)^* E(u) - 1 ||_2 <= 2 || E(u) - u ||_2` by
  `|| ab ||_2 <= || a ||_op || b ||_2`).  The internal sequence `(u'_m)`
  is an element of the operator-norm ultraproduct `A`, exactly
  `H`-central at every level: this is the same average-then-polar
  mechanism as `kazhdan-subgroup-weak-ucp-exactification-proof`.  That
  group averages `Ad rho(mu^n)(u)` converge to `E(u)` only in the Hilbert
  norm of `L^2(M_d)` is irrelevant -- the limit exists levelwise, and no
  limit is taken inside `A`.  What the column step really needs, and what
  no projection supplies, is the JOINT exactness of the remaining
  Steinberg relations with the commutant membership: for the column
  `V = Z^(n-1)` with Levi `L = SL_(n-1)(Z)` acting by a genuine `rho`,
  put `u_1 in rho(Stab_L(e_1))'` (exact, by the above) and
  `u_x := rho(gamma) u_1 rho(gamma)^(-1)` for `x = gamma e_1` (well
  defined on primitive vectors precisely because of that exactness); the
  column is an exact `rho`-equivariant representation iff, in addition,
  `[u_(e_1), u_(e_2)] = 1` and `u_(e_1) u_(e_2) = u_(e_1 + e_2)` hold
  EXACTLY in operator norm.  Each is an exact relation among
  `rho`-conjugates of the single unitary `u_1`; projecting onto one
  commutant destroys the others.  So the honest residue of the column
  step is relative flexible HS-stability of the affine group
  `Z^(n-1) rtimes SL_(n-1)(Z)` with the Levi held exact -- one unitary
  and finitely many exact relations, not the production of invariant
  elements -- and the row step and the column-row Steinberg commutators
  `[x_(in), x_(nj)] = x_(ij)` repeat the same shape.  Amenable
  HS-stability exactifies `V` alone and the projection exactifies the
  commutant alone; the open content is doing both at once.
