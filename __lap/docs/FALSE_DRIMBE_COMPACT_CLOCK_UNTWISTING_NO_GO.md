# Drimbe untwists the compact clock target completely

Date: 2026-08-11

## 1. Outcome

Drimbe's coinduced-action theorem is stronger in its target than the
countable-target version of Ioana's profinite theorem: it applies to every
group in `U_fin`, and in particular to compact Polish groups.  Nevertheless
it does not construct the missing three-moment Schreier system.  For the
natural inverse-limit Baumslag--Solitar clock target it proves the opposite:
every such cocycle is a coboundary.

More generally, let `A` be a countable property-`(T)` group, let `B<A` have
infinite index, and let

`A curvearrowright X=X_0^(A/B)`                            `(DCU1)`

be a coinduced pmp action covered by Drimbe's Theorem A.  If `V` is an
amenable torsion-free compact Polish group, then every measurable cocycle

`omega:A times X -> V`                                   `(DCU2)`

is a measurable coboundary.

For odd `p`, this applies to the compact metabelian clock group

`B_hat_p = Z_p semidirect_(1+p) Z_p`,                    `(DCU3)`

the inverse limit of the finite groups

`B_k=<h_k,c_k | h_k^(p^(k+1))=c_k^(p^k)=1,`
`                 c_k h_k c_k^(-1)=h_k^(1+p)>`.          `(DCU4)`

Consequently a coherent `B_hat_p`-valued cocycle on a Drimbe coinduced
action cannot carry a nonzero primitive clock class.  After reduction to
every `B_k`, its transition table can be gauged to the identity.  The
primitive scalar holonomy required by the fold is therefore incompatible
with this compact-target/coinduced shortcut.

This sharpens `FALSE_IOANA_DRIMBE_SCHREIER_SCOPE_AUDIT.md`: the problem is
not that Drimbe only treats countable targets.  Compact targets are allowed.
The obstruction is that the relevant compact clock target is too amenable
and too torsion-free; superrigidity annihilates the cocycle instead of
producing useful Archimedean control.

## 2. An amenable torsion-free target corollary

Recall Drimbe's theorem in the property-`(T)` case.  Let `A` be countable,
let `B<A`, and let `H<A` have relative property `(T)`.  Assume no finite-index
subgroup of `H` is contained in a conjugate of `B`.  For a coinduced action
as in `(DCU1)`, every cocycle with values in a `U_fin` group is cohomologous
on `H` to a homomorphism.  If `H` is w-normal, the homomorphism is defined on
all of `A`.  In particular, when `A=H` has property `(T)` and `B` has infinite
index, every coinduced action from `B` is `U_fin`-cocycle superrigid.

All compact Polish groups belong to `U_fin`.

**Theorem 1 (torsion-free amenable target untwisting).**  In the last
property-`(T)` setting, let `V` be an amenable torsion-free compact Polish
group.  Then every measurable cocycle `(DCU2)` has the form

`omega(g,x)=phi(gx)^(-1) phi(x)`                         `(DCU5)`

after choosing one of the two standard cohomology conventions, for a
measurable map `phi:X->V`.

### Proof

Drimbe's theorem gives a measurable transfer `phi` and a homomorphism

`delta:A->V`                                            `(DCU6)`

such that `omega` is cohomologous to `delta`.  The image `delta(A)` is a
quotient of the discrete property-`(T)` group `A`, hence has property `(T)`
as a discrete group.  It is also a subgroup of the amenable group `V`, so it
is amenable.  An amenable discrete property-`(T)` group is finite.  Since
`V` is torsion-free, its only finite subgroup is trivial.  Therefore
`delta=1`, and the cohomology formula is exactly `(DCU5)`.  End proof.

Compactness is used only to place `V` in `U_fin`; the same proof applies to
any amenable torsion-free target already known to lie in `U_fin`.

## 3. The inverse-limit clock group is torsion-free

Fix an odd prime `p` and put `q=1+p`.  With the natural reduction maps, the
inverse limit of `(DCU4)` is the pro-`p` semidirect product `(DCU3)`.  In
coordinates its multiplication is

`(u,a)(v,b)=(u+q^a v,a+b)`,                            `(DCU7)`

where the continuous `p`-adic power `q^a` is defined because
`q in 1+p Z_p`.

**Lemma 2.**  `B_hat_p` is metabelian, compact, and torsion-free.

### Proof

It is a semidirect product of two copies of the compact abelian group
`Z_p`, so it is compact and metabelian.  Suppose `(u,a)^n=1` for an integer
`n>=1`.  Projection to the second coordinate gives `na=0` in `Z_p`.
The additive group `Z_p` is torsion-free, hence `a=0`.  Equation `(DCU7)`
then gives `(u,0)^n=(nu,0)=1`, so `u=0`.  End proof.

The odd-prime assumption avoids the separate choice of the standard
torsion-free analytic subgroup of `Z_2^x`; the fold-aligned construction is
free to use odd `p`.

**Corollary 3 (compact clock cocycles are trivial).**  Every measurable
`B_hat_p`-valued cocycle for a property-`(T)` coinduced action covered by
Drimbe is a coboundary.

This follows from Theorem 1 because `B_hat_p` is metabelian and hence
amenable, and Lemma 2 gives torsion-freeness.

## 4. Finite reductions and the three moments

Let

`pi_k:B_hat_p -> B_k`                                  `(DCU8)`

be the natural quotient.  If `(DCU5)` holds, then the finite transfer

`phi_k=pi_k composed_with phi:X->B_k`                  `(DCU9)`

gauges `pi_k composed_with omega` to the identity exactly as a measurable
cocycle.  Therefore its two centered clock coordinates are identically
zero after measurable gauge.  In particular the measurable analogues of

`R_(*,k)/M_k`, `A_(*,k)/M_k`,
`R_(*,k)A_(*,k)/M_k`                                  `(DCU10)`

all vanish identically, not merely asymptotically.

This conclusion is not the desired FALSE construction.  A primitive fold
requires a nontrivial gauge-invariant order-`p` holonomy.  A coboundary has
none.  Equivalently, if a proposed compatible family of finite transition
tables has the primitive clock evaluation at every level, then that family
cannot be the reductions of a `B_hat_p`-valued cocycle on this coinduced
action.

One can approximate each finite-valued measurable transfer `(DCU9)` in
measure by a cylinder function.  For a fixed finite generator set, the
resulting transition table is trivial off a set of arbitrarily small
measure.  This yields finite-cylinder moment estimates inside the pmp
model, but it still does not manufacture finite Schreier quotients of the
Kun--Thom pair.  Coinduction and finite Shapiro induction are different
operations.

## 5. Consequence for the real FALSE gate

There are now two rigorous exclusions around the three-moment proposal.

1. On the actual primitive scalar principal bundle, property `(T)` forces
   a linear centered moment for some fixed generator, as proved in
   `FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md`.
2. Replacing the changing finite targets by the coherent compact target
   `(DCU3)` on a Drimbe coinduced action makes the cocycle a coboundary and
   erases the primitive holonomy altogether.

Thus Drimbe's theorem does not bridge the gap between the scalar clock and
the required base-dependent paired Fourier/Frobenius model.  The remaining
object is still an explicitly nonliftable relative-holonomy system:

* it cannot encode the primitive class as one scalar transition coordinate;
* it cannot arise from an amenable torsion-free compact-target cocycle on a
  cocycle-superrigid coinduced action; and
* it must retain the marked fold through changing polarizations or
  higher-incidence cancellation.

No such system, and hence no proof of the three real moment limits, has yet
been constructed.

## 6. Reference

Daniel Drimbe, *Cocycle and orbit equivalence superrigidity for coinduced
actions*, Ergodic Theory Dynam. Systems 38 (2018), arXiv:1512.00093,
Theorem A and Definition 1.1.  The paper explicitly records that compact
Polish groups belong to `U_fin`.
