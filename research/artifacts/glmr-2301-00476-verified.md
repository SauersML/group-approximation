# Verification record: Glebsky--Lubotzky--Monod--Rangarajan, *Asymptotic cohomology and uniform stability for lattices in semisimple groups*

arXiv:2301.00476.  Abstract read from the arXiv listing this session
(cairn-quotient-mf, 2026-08-14).  This closes the gap flagged in
`research/torsion-free-finitely-presented-non-mf.md`, which recorded
"abstract read, theorem statements not".

## Abstract (as displayed on the listing)

> It is, by now, classical that lattices in higher rank semisimple groups
> have various rigidity properties.  In this work, we add another such
> rigidity property to the list: uniform stability with respect to the family
> of unitary operators on finite-dimensional Hilbert spaces equipped with
> submultiplicative norms.  Namely, we show that for (most) high-rank
> lattices, every finite-dimensional unitary "almost-representation" of
> `Gamma` is a small deformation of a (true) unitary representation.

## What is and is not established here

**Established:** the property proved is *uniform* stability, and the class is
lattices in higher-rank semisimple groups.

**NOT established here:** the numbered theorem statements were not read from
the body, so neither the precise definition of "almost-representation" used
there nor the exact class covered by "(most) high-rank lattices" is verified
at source level.  In particular, whether `Z^3 semidirect SL_3(Z)` — a lattice
in the *non*-semisimple group `R^3 semidirect SL_3(R)` — is covered is
**unresolved** by this record.  Anyone needing that must read the body.

## Why the coverage question is moot for this repository's fork

Independently of which groups are covered, uniform stability cannot be
applied to a corona representation of an infinite group: see
`corona-defect-is-not-uniform`.  The defect of the coordinate maps of a
corona representation vanishes pointwise and need not vanish uniformly, which
is the hypothesis every uniform-stability theorem takes.  The applicable
notion is instead *matricial* stability in the sense of Dadarlat
(Adv. Math. 2021, doi:10.1016/j.aim.2021.107722, already cited by the
manuscript), which is stated exactly for lifting homomorphisms into the
matrix corona.
