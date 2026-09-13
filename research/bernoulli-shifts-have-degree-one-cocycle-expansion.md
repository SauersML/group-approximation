---
rg: 2
id: bernoulli-shifts-have-degree-one-cocycle-expansion
kind: claim
title: The Bernoulli shift of Sp_4(Z) has degree-one cocycle expansion with finite abelian coefficients
distinct_from:
  deligne-class-congruence-cosystole-bounded-below: that is a degree-two cosystolic bound for one class on congruence covers; this is a degree-one stability property of the Bernoulli shift, independent of any class or finite quotient.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

**OPEN.** Let `Gamma = Sp_4(Z)` (or its torsionfree `Gamma(3)`) with a finite presentation `<S | R>`, and `A` finite
abelian. There is a rate `rho` with `rho(eps) -> 0` such that every measurable `c : S x [0,1]^Gamma -> A` whose
relator sums are nonzero on measure at most `eps` agrees, off measure `rho(eps)` on each generator, with an exact
1-cocycle `Gamma x [0,1]^Gamma -> A`. The property does not depend on the presentation, up to changing `rho`.

**Payoff.** By `degree-one-bernoulli-expansion-excludes-weak-lifts`, it proves
`deligne-triple-cover-no-weakly-bernoulli-liftable-action`, and with it the corresponding case of the Rokhlin
ascent obstruction for `E_3`.

**Model test.**
- **Free groups.** No 2-cells, so expansion holds with `rho = 0`.
- **`Z^2` (heuristic, not w-rigid).** Pairing sparse point defects by strings suggests `rho(eps) ~ sqrt(eps)`: a
  nonlinear rate, but still a rate.
- **What a failure would mean.** Approximate A-extensions of the Bernoulli shift staying far from exact ones.
  Weakly Bernoulli lifts of Deligne's class would produce exactly such cochains, through `b(x) - b(x')`.

## Attempts

- **Property (T) (ex2-rokhlin-almost-cocycle, 2026-09-13).** Popa's local rigidity compares exact cocycles that are
  close on generators. It gives nothing for approximate cocycles, which define no unitary representation.
- **Filling reformulation.**
  - `e = delta c` is a sparse exact 2-cocycle on each orbit complex, and expansion asks for a measurable equivariant
    primitive of density `rho(eps)`.
  - Recalled, not checked: `Sp_4(Z)` is a duality group of dimension 4 (Borel--Serre), so finite exact 2-cocycles on
    the universal cover have finite primitives.
  - Missing: quantitative filling bounds in that dimension for the non-cocompact `Sp_4(Z)`, and a Borel selection of
    local fillings for infinite membrane supports.
- **Finite actions.** The analogous statement on congruence quotients is Gohla--Thom "expansion in dimension 1". It is
  known on Bruhat--Tits quotients through Kaufman--Kazhdan--Lubotzky and Evra--Kaufman, and not known for real rank-2
  covers.
