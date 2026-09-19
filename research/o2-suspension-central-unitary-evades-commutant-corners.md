---
rg: 2
id: o2-suspension-central-unitary-evades-commutant-corners
kind: claim
title: The winding unitary of the unitized O_2-suspension is a nontrivial central unitary in a matrix corona that every commutant corner trace misses
invalidates:
  - lifted-thompson-t-eigencorners-via-projection-extraction
  - torsion-free-non-mf-from-infinite-order-mark
distinct_from:
  commutant-projection-extraction: that claim asserts that trace-invisible central unitaries are trivial. This claim gives an explicit nontrivial one and so refutes it.
  corona-corner-detection-criterion: that claim reduces corner detection to a relative-commutant question. This claim exhibits a corona representation in which the question has a negative answer at every spectral point other than 1.
  mf-invariant-corner-visibility: that claim concerns a trace gap in some convenient realization. This claim fixes one realization in which every tracial state of every commutant corner is blind to the mark.
  central-eigencorners-die-over-full-radical-quotients: that claim kills eigencorners that already exist, over quotients with full radical. This claim shows that eigencorners need not exist at all for a nontrivial central unitary.
  bounded-rank-corners-excluded: that claim excludes corners of bounded rank for Kazhdan sources. This claim excludes corners of every rank, for a group chosen as a generating unitary group of a traceless-off-1 MF algebra.
---

**ESTABLISHED.**  Let `J = C_0((0,1), O_2)` and let `C = J + C·1` be its
unitization.  Put `u = e^{2 pi i t} ⊗ 1`, so `u` is a unitary of `C` with
`u - 1 = (e^{2 pi i t} - 1) ⊗ 1 ∈ J`.  Then:

1. `u` is central in `C`, `‖u - 1‖ = 2` and `sp(u) = T`.
2. There are a norm matrix corona `Q = prod_k M_(d_k) / (+)_k M_(d_k)` and a
   unital isometric *-homomorphism `iota : C -> Q`.
3. Every tracial state of `C` vanishes on `J`.

Let `H` be any countable subgroup of `U(C)` that contains `u` and generates
`C` as a C\*-algebra; one exists because `C` is separable.  Put
`Theta = iota|_H : H -> U(Q)`, `eps = u ∈ Z(H)` and
`B = Theta(H)' ∩ Q = iota(C)' ∩ Q`.  Then

    for every nonzero projection q ∈ B and every tracial state tau of qQq:
    ‖q Theta(eps) q - q‖_(2,tau) = 0,

but `Theta(eps) != 1`.  Moreover, for every nonzero projection `q ∈ B` and
every `lambda ∈ C`,

    ‖(Theta(eps) - lambda) q‖ >= |lambda - 1|,

so no approximate eigencorner exists at any spectral point `lambda != 1`.

Both forms of [[commutant-projection-extraction]] are therefore false: the
statement and its contrapositive. The configuration is exactly the one the
target identified as the only survivor: `sp(Theta(eps))` is the whole circle,
all the trace mass sits at `1`, and the operator-norm defect is `2`.

The proof is in `o2-suspension-central-unitary-evades-commutant-corners-proof`.

## What this kills, and what it does not

- `lifted-thompson-t-eigencorners-via-projection-extraction` applies the
  general extraction claim with `H = T̄`. Its only prerequisite is now false,
  so the route is dead as written. The target
  `lifted-thompson-t-centre-has-commutant-eigencorners` stays OPEN. Its one
  live route goes through the torus-knot group `K(3,4)`, whose input is
  specific to that group.
- `torsion-free-non-mf-from-infinite-order-mark` needs extraction for the
  central mark of an arbitrary torsion-free group. It is dead as written.
- The claim is not refuted for any **specific** group. For a given `H` the
  question is still open.

**Obstruction, stated precisely.**  The only information that
`commutant-projection-extraction` takes from `H` is this: the mark is
central, and every corner trace misses it. The counterexample shows that
this information is consistent with a nontrivial mark. Every commutant corner
trace of `Theta` factors through a tracial state of `C*(Theta(H))`, and those
states see only the tracial part of that algebra. A purely infinite fibre
(here `O_2`) over the arc `sp(u) \ {1}` is invisible to all of them, but it
is still MF, by Gabe's Corollary B. So any proof of central eigencorners, for
`T̄`, for `K(3,4)` or for any mark group, must use input specific to the
group, such as stability, property (T) of a normal subgroup containing the
mark, or finite spectrum. It must rule out this traceless-fibre
configuration for that group's representations.

**Where the lifted-Thompson gap now sits.**  Suppose `T` has full MF
radical. Items 1 and 3 of
`central-eigencorners-die-over-full-radical-quotients` then say the
following about any corona representation `rho` of `T̄` with
`rho(z) != 1`:

- it has no exact central eigencorner at any `lambda != 1`;
- no point of `sp(rho(z)) \ {1}` is isolated.

So an MF witness for `T̄` would carry its central winding on non-isolated
spectrum off `1` with no eigencorner. This example shows that this
configuration is consistent for a general countable group. It is even
consistent with every corner trace missing the mark. So the input still
missing for `lifted-thompson-t-is-not-mf` must be specific to `T̄`. It has
to exclude a continuous field of `z`-twisted representations of `T` whose
fibres over `sp(rho(z)) \ {1}` carry the winding with no eigencorner. This
note does not decide whether `T̄` has such fields, and does not decide
whether their corner traces see `z`.

Consequence for the reduction in `commutant-projection-extraction`: pass to
a free ultrafilter `omega`. The maps below have `‖E_k(a)‖ -> ‖a‖`, so the
same `iota` stays isometric into `A_omega = prod_omega M_(d_k)`. The argument
applies verbatim there. Hence `iota(C)' ∩ A_omega` has no nonzero projection
in the hereditary subalgebra of `f(u)` for any bump `f` that vanishes near
`1`. In particular, relative commutants of countable groups in a matrix norm
ultraproduct need not have real rank zero, even along a central unitary.
