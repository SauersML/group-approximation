---
rg: 2
id: genus-three-torelli-second-homology-infinitely-generated
kind: claim
title: "The second integral homology of the genus three Torelli group is infinitely generated"
---

`H_2(I_3; Z)` is not a finitely generated abelian group, where
`I_3 = ker(Mod(S_3) -> Sp_6(Z))`.

Source of the conjecture: A. A. Gaifullin, *On spectral sequence for the action of
genus 3 Torelli group on the complex of cycles*, arXiv:2011.00295, Izv. Math. 85:6
(2021), 1060–1127. His abstract (read 2026-09-13) states that the term `E^3_{0,2}`
of the spectral sequence for the action of `I_3` on the complex of cycles is
infinitely generated. That is, `E^1_{0,2}` stays infinitely generated after
quotienting by the images of `d^1` and `d^2`. The abstract presents this as
evidence toward `H_2(I_3; Z)` being infinitely generated and `I_3` not being
finitely presented; what remains is the quotient by the image of `d^3`.

## Attempts

- **Kill the last differential (Gaifullin's program).** The spectral sequence of
  the action on the contractible complex of cycles has
  `E^1_{p,q} = ⊕_{σ} H_q(Stab σ; Z_σ)` over orbit representatives of `p`-cells,
  converging to `H_{p+q}(I_3; Z)`. In a first-quadrant homological spectral sequence,
  the only differentials into `E_{0,2}` are `d^r: E^r_{r,3-r} -> E^r_{0,2}` for
  `r = 1, 2, 3`, and none leave it. So `E^∞_{0,2} = E^3_{0,2}/im(d^3)` with
  `d^3: E^3_{3,0} -> E^3_{0,2}`. `E^∞_{0,2}` is the bottom filtration piece of
  `H_2(I_3; Z)`, a subgroup, and a subgroup of a finitely generated abelian group
  is finitely generated. Hence **if `E^3_{0,2}/im(d^3)` is infinitely generated, then
  `H_2(I_3; Z)` is infinitely generated.** Where it dies: `E^3_{3,0}` is a subquotient
  of `E^1_{3,0}`, a direct sum over infinitely many orbits of 3-cells, so `d^3` has an
  infinitely generated source and could a priori absorb `E^3_{0,2}`. Controlling it
  needs an explicit description of `E^3_{3,0}` and of `d^3` on it.
- **Detect classes by abelian cycles.** Infinite generation of `E^∞_{0,2}` could be
  certified by infinitely many independent homology classes of `I_3` supported on
  cell stabilizers (for example abelian cycles from commuting separating twists or
  bounding-pair maps), shown independent by evaluating cohomology classes pulled
  back from finite or abelian quotients. Status: not attempted in detail. The
  abelian-cycle vocabulary is the one used for `H_2` of the genus 3 hyperelliptic
  Torelli group by Spiridonov (arXiv:2601.12605, abstract).
