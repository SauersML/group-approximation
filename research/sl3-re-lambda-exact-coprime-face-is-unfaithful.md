---
rg: 2
id: sl3-re-lambda-exact-coprime-face-is-unfaithful
kind: claim
title: No relative matrix embedding of the SL3 lattice pair has coprime-level exact lattice microstates
distinct_from:
  arithmetic-pair-is-not-relatively-embeddable: That is the full non-relative-embedding statement over all microstate sectors; this closes the coprime exact lattice face among matrix-form witnesses for the SL3 pair.
  odd-congruence-lambda-exact-sector-collapses: That proves relative-commutant collapse on the coprime exact lattice sector; this combines it with uniform Kazhdan control of arbitrary matrix carriers to exclude relative matrix witnesses without a rate assumption.
artifacts:
  - research/artifacts/kazhdan-carrier-uniformization-2026-09-08.md
---

Let `Lambda=SL_3(Z)<=Gamma=SL_3(Z[1/p])`, with `p` prime, and
`h=diag(p,1,p^-1)`. A relative matrix witness consists of a canonical
trace embedding `pi:Gamma->prod_omega M_(d_k)` with unitary
representatives `pi_k(g)` and unital subalgebras `B_k subset M_(d_k)`
satisfying

    dist_2(pi_k(c),B_k)->0                 (c in Lambda),
    ||E_(B_k)(pi_k(g))||_2->0             (g outside Lambda).

Call the witness **lattice-exact of coprime type** if the restriction
`pi|_Lambda` has exact coordinate representatives `sigma_k` factoring
through `SL_3(Z/n_k)` with `gcd(n_k,p)=1`.

No such witness exists, regardless of the levels, multiplicities, or
the rate at which the source containment defects vanish.

The proof combines the exact congruence-slot identity from
`odd-congruence-lambda-exact-sector-collapses` with
`kazhdan-generators-control-matrix-algebra-distance`. For a fixed
Kazhdan generating set `S` with constant `kappa`, it gives

    dist_2(pi_k(h),B_k)
      <= ||pi_k(h)-sigma_k(h mod n_k)||_2
         +(2/kappa)sqrt(sum_(s in S)dist_2(sigma_k(s),B_k)^2)
      ->0.

Thus `||E_(B_k)(pi_k(h))||_2->1`, a contradiction. No factor
`log n_k` occurs. Equivalently, Haar averaging in `U(B_k')`
would turn the vanishing outside expectation into a lattice-central
unitary moved by `pi(h)` in the same actor embedding, contradicting
established sector collapse.

The rank-three arithmetic input uses two independent Weyl directions;
the argument does not establish the rank-two counterpart. Coprimality
is needed to define the congruence slot of `h`. The theorem does not
eliminate arbitrary approximate lattice tuples or unresolved primary
sectors, and does not prove the full non-relative-embedding target.

The named target has the displayed matrix witness scope. The independent
Jones-projection proof, `sl3-re-coprime-face-closes-by-jones-kazhdan`,
also excludes finite tracial coordinates carrying the same prescribed
exact finite congruence images, with the sharper bound
`dist_2(pi_k(h),B_k)<=eta_k+2 max_s dist_2(sigma_k(s),B_k)/kappa`.
Gao's general definition allows QWEP coordinates and hyperfinite carriers;
neither proof makes an arbitrary Gao witness coordinate-exact on the
lattice.

## Proof history

The 2026-08-21 audit correctly invalidated
`sl3-re-coprime-face-unfaithful-proof`: a moving congruence slot need
not belong to the constant-sequence algebra `pi(Lambda)''`.
`congruence-slot-escapes-ultraproduct-lambda-algebra` remains valid,
and that route remains invalidated. The logarithmic-rate theorem
was a valid partial repair.

The 2026-09-08 route
`sl3-re-coprime-face-from-kazhdan-carrier-control` closes the entire
matrix face by controlling the full coordinate algebra uniformly.
The independently supplied Jones-projection route proves the same
exclusion through uniform containment of the group unitaries.
It does not revive the false algebra identification. Slow source
containment is therefore no longer an unresolved coprime sector.
