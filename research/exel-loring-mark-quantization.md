---
rg: 2
id: exel-loring-mark-quantization
kind: claim
title: The Exel--Loring winding number pins the phase of an infinite-order central mark
distinct_from:
  exel-loring-relative-quasirep-invariant: that claim records the external invariant and its nontriviality theorem; this one is the specific deployment against a central mark, with the primary text read and the two blocking hypotheses identified.
  commutant-projection-extraction: that asks for a projection cutting a corner; this asks for an integer-valued pairing, and the two attack complementary halves of the same residual case.
  corona-corner-detection-criterion: that claim is established and reduces the central branch to a connected spectrum; this one attacks the case it leaves open.
---

Let `1 -> Z -> Gtilde -> Gamma -> 1` be a central extension with class
`c in H^2(Gamma; Z)`, let `x in H_2(Gamma; Z)` be represented by a product
of commutators `prod_{i<=g} [a_i, b_i]` that is trivial in `Gamma`, and
suppose the pairing `<c, x> = k != 0`, so that the lifted product of
commutators equals `zeta^k` in `Gtilde`.  Suppose also that `Gtilde` carries
the Kazhdan compression data with `zeta` in the normal closure of the
compression defect.  Then every corona representation of `Gtilde` kills
`zeta`: the Exel--Loring winding number of the lifted model forces the trace
of the argument of the mark to equal a K-theoretic pairing, transport forces
the mark to be Hilbert--Schmidt invisible so that trace vanishes, and the
group data make the pairing nonzero.  Consequently, if `zeta != 1` then
`Gtilde` is not MF.

This is a **programme, not a theorem**.  Two hypotheses of the published
formula are not currently met by the intended application, and they are
stated precisely below.

## Ideas

**What the primary text actually says.**  Dadarlat, *Quasi-representations
of groups and two-homology*, arXiv:2111.05755v1, read this session.
Theorem 1.1, verbatim in content: for `Gamma` countable discrete and
`x in H_2(Gamma,Z)` represented as above, there are a **finite set**
`S subset Gamma` and `eps > 0` — both independent of the dimension — such
that every unital `pi : Gamma -> U(n)` with
`‖pi(st) - pi(s)pi(t)‖ < eps` for `s,t in S` satisfies

    pi_# (alpha_Gamma(x)) = wn det( (1-t) 1_n + t prod_i [pi(a_i), pi(b_i)] )
                          = (1/2 pi i) Tr log( prod_i [pi(a_i), pi(b_i)] ).

Equation (3) of the same paper gives the tracial form: for `A` unital with
trace `tau` and `pi : Gamma -> U(A)` with the same defect bound,
`tau_*(pi_#(alpha_Gamma(x))) = (1/2 pi i) tau(log(prod_i [pi(a_i), pi(b_i)]))`.
A norm matrix corona carries the trace `lim_omega tr_{d_n}`, so the tracial
form is available on exactly the target of this program.  Theorem 3.2 is the
nontriviality statement: if `Gamma` is quasidiagonal, admits a
`gamma`-element, and `x` has infinite order in `H_2`, then some
quasi-representation has nonzero winding number, hence is not perturbable to
a representation (Corollary 3.3).

**Why this is the right shape.**  The formula measures a relation that holds
in the group but only approximately in the model — which is precisely the
compression defect.  Its value is an integer, so it is a natural home for a
mark of infinite order, where a two-point spectrum is unavailable.  It is
also relative, pairing the mark against an `H_2` class rather than looking
at the mark alone, which is the only shape `matrix-corona-k1-vanishes`
leaves open; and by `matrix-corona-k0-index-survives` such classes do
survive the corona quotient.

**Blocker 1: the quasi-representation is not multiplicative enough.**
Lifting a corona representation of `Gtilde` through `Gtilde -> Gamma` gives
a map `pi` whose multiplicative defect is `Theta(zeta)^{c(s,t)} - 1`.  That
is small in operator norm only if the mark is close to `1` in operator norm
— the opposite of the separation one is trying to contradict.  The escape is
the near-scalar case: if `Theta(zeta)` is within `delta` of a scalar
`lambda`, the lift is a **projective** quasi-representation with cocycle
`lambda^c`, and one needs a twisted form of Theorem 1.1.  Note where this
lands: `corona-corner-detection-criterion` proves the spectrum of the mark
is a connected arc through `1` or the whole circle, and the near-scalar case
is exactly the arc case that the corner method cannot close.  **The two
tools attack complementary halves of the same residual case**, which is the
main reason to keep this programme alive.

**Blocker 2: the nontriviality theorem points the wrong way.**  Theorem 3.2
assumes `Gamma` **quasidiagonal**, and a quasidiagonal group is MF.  So the
published nontriviality criterion can never be applied to a non-MF
candidate: its hypothesis contradicts the conclusion being sought.  What
this repository can take from the paper is Theorem 1.1 and equation (3),
which assume nothing about `Gamma` beyond countability; nonvanishing of the
pairing for the candidate group would have to be proved separately.  This
corrects the framing in `exel-loring-relative-quasirep-invariant`: the
second Betti number hypothesis is not a hurdle for us to clear, because the
theorem carrying it is unusable here in either case.

**A genuine incompatibility, worth recording.**  The mark needs
`<c, x> != 0` for some `x in H_2(Gamma;Z)`, which forces `c` to have
infinite order and hence a nonzero image in `H^2(Gamma; Q)`.  By Dadarlat,
*Obstructions to matricial stability of discrete groups and almost flat
K-theory*, arXiv:2007.12655 (abstract read), matricial stability — finite
dimensional approximate unitary representations perturbable to genuine ones
in the **point-norm** topology — implies vanishing of rational cohomology in
all nonzero even dimensions, for large classes of groups.  So a base group
carrying a usable Exel--Loring mark is, for those classes, **not** matricially
stable.  The Exel--Loring route and the stability route of
Bachner--Dogon--Lubotzky are therefore mutually exclusive on the same base
group.  This also explains why Bachner--Dogon--Lubotzky's condition (`*`) is
a mixed operator-to-Hilbert--Schmidt statement rather than a point-norm one:
the point-norm version is obstructed exactly where their marks live.

**Hedge resolved, and the narrowing is by a checkable property.**  The
primary text has since been read (cairn-scout, recorded at
`research/dadarlat-matricial-stability-obstruction.md`).  Two hypotheses
carry the theorems: **weak quasidiagonality** and a `gamma`-element, the
latter following from uniform embeddability and rarely binding.  The
binding one is weak quasidiagonality, and for Kazhdan groups it is governed
by Dadarlat's Proposition 3.19, attributed to Ozawa--Thom: an infinite
property-(T) group that is weakly quasidiagonal has an infinite residually
finite quotient.  So an infinite Kazhdan group with no infinite residually
finite quotient — the minimally almost periodic regime — falls outside the
theorems entirely, while **linear** Kazhdan bases are covered by
Corollary 1.3 and are inside.

The incompatibility recorded above therefore holds on linear Kazhdan bases,
such as `SL_3(Z)` and `Z^3 semidirect SL_3(Z)`, and does **not** apply to a
minimally almost periodic base.  Since minimal almost periodicity is
precisely the regime the rest of this cluster is being pushed into, the
practical reading is that the Exel--Loring route and the stability route
stop being mutually exclusive exactly where this program wants to work — so
the constraint governs route selection over linear bases and is silent over
the candidate that matters.
