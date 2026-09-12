---
rg: 2
id: two-power-sector-conjugator-dichotomy-proof
kind: route
title: The conjugator is an almost-central bimodule vector, and Kazhdan rigidity converts almost to exact
target: two-power-sector-conjugator-dichotomy
requires: []
---

**Part 1 (moment equality and non-amenability).**  The identity
`w(B) = h w(A) h^(-1)` holds over `Z[1/2]` because `B_i = h A_i
h^(-1)` entrywise (`h e_(ij)(r) h^(-1) = e_(ij)((d_i/d_j) r)` with
`d = (2,1,1/2)`, and the chosen levels `2, 4, 2` make every `B_i`
integral).  For a fixed word `w`: if `w(A) = 1` then `w(B) = 1`
(conjugate matrices); if `w(A) != 1` then both `w(A)` and `w(B)` are
fixed integer matrices different from `1`, hence `!= 1 mod 2^a` for
all large `a`.  So along any 2-power tower the traces of fixed words
agree in the limit, which is the equality of mixed `*`-moments of
`pi(A)` and `pi(B)` in `M`.  `Lambda_0 = <A>` contains the upper
elementary matrices at level one and the lower ones at levels
`2, 4, 2`, hence contains a relative elementary congruence subgroup
of `SL_3(Z)`; by the congruence-era normal generation results
(Bass--Milnor--Serre; Tits) such a subgroup has finite index, so
`Lambda_0` is a finite-index subgroup of `SL_3(Z)` and has property
(T) with Kazhdan set its generating tuple `A`.  Its group von
Neumann limit is non-amenable, so Jung's theorem (uniqueness of
embeddings up to conjugacy holds exactly for amenable algebras)
gives no conjugacy for free.

**Part 2 (the dichotomy).**  Define two unitary representations of
`Lambda_0` on `L^2(M)`-bimodule style: for `s = A_i` a generator,
`rho_1(s) xi = pi(A_i) xi` and `rho_2(s) xi = xi pi(B_i)^*`,
extended multiplicatively (both are genuine commuting unitary
representations of `Lambda_0` on `L^2(M)`, using that
`A_i mapsto B_i` extends to the isomorphism `Ad(h)` of `Lambda_0`
onto `<B>`).  The combined representation `rho(s) = rho_1(s)
rho_2(s)` sends `xi` to `pi(A_i) xi pi(B_i)^*`.  A unitary `V` with
intertwining defect `max_i || V pi(A_i) V^* - pi(B_i) ||_2 = eta`
is, as a unit vector of `L^2(M)`, `(A, eta)`-almost-invariant for
`rho`: `|| rho(s) V - V ||_2 = || pi(A_i) V pi(B_i)^* - V ||_2 =
|| pi(A_i) V - V pi(B_i) ||_2 <= eta`.  Property (T) of `Lambda_0`
with Kazhdan pair `(A, epsilon_0)`: if `eta < epsilon_0 / 2` (say),
there is a `rho`-invariant vector `xi` with `|| xi - V ||_2 <= 2
eta / epsilon_0 < 1`; invariance reads `pi(A_i) xi = xi pi(B_i)`
for all `i`.  Then `xi^* xi` commutes with every `pi(B_i)` and
`xi xi^*` with every `pi(A_i)`; since `|| xi - V ||_2 < 1` with `V`
unitary, `xi` has trivial kernel support in the sense that `|xi|`
is bounded below on a projection of trace `> 0`... more simply:
with `eta := max_i` defect, the (T) estimate gives the invariant
`xi` with `|| xi - V ||_2 <= eta / epsilon_0`.  The polar part
`U_0 in M` of the square-integrable operator `xi` is a partial
isometry with `pi(A_i) U_0 = U_0 pi(B_i)` (since `xi^* xi` commutes
with every `pi(B_i)`, its functional calculus does too), and its
support projections have trace at least `1 - (eta/epsilon_0)^2`
(the defect of `xi` from the unitary `V` bounds the co-support).
So: EITHER every unitary of `M` has defect `>= delta_0 :=
epsilon_0/2`, OR there are exact partial intertwiners with
co-supports of arbitrarily small trace (as witnesses with smaller
`eta` are fed in) [AUDIT 2026-08-21: no mechanism supplies smaller witnesses for a fixed `M`; this proves only the class-level statement -- see the claim's Attempts for the tiling-plus-saturation repair]; in the second case a diagonal argument across
the tower class (reindexing the ultraproduct, as usual in this
lane) produces an exact UNITARY conjugator in an ultraproduct of
the same 2-power class.  At the level of the sector question --
which quantifies over all such towers -- this is the dichotomy
`(CD1)`: a uniform finite-level floor for the whole class, or an
exact conjugator somewhere in the class; and an enemy's corrector
is an exact conjugator outright, so an enemy requires the second
branch.

**Part 3 (the torsor and the selection).**  If `V_infty` conjugates,
then any other conjugator `V'` gives `V_infty^* V' in
pi(B)(Lambda_0)' cap M =: C`, and conversely `V_infty u` conjugates
for every unitary `u in C`: the conjugators form the torsor
`V_infty U(C_A)` with `C_A = pi(A)(Lambda_0)' cap M` (NOT `U(C)` on the right with the B-side commutant, as first printed: `V_infty^* V'` commutes with `pi(A)`).  Substituting `V = V_infty u` into the remaining
enemy constraints (Weyl inversion `pi(w_13) V pi(w_13)^(-1) =
V^(-1)`, the three-term relation, commutation of the Weyl orbit,
`tr(V^j) -> 0`, mixed-word regularity) produces equations in `u`
whose coefficients are the fixed unitaries
`V_infty^(+-1)` and `pi(Weyl)`-conjugates: a twisted cocycle system
for the `S_3`-action on `U(C)`.  Solvability of that system is
exactly what separates a conjugacy-branch world from an enemy, and
is the selection problem named in the claim.
