# Dual-orbit rigidity for the binary Leavitt ring

Date: 2026-08-13

## 1. Outcome

Let

\[
 R=L_{\mathbb F _2}(1,2),\qquad Q=R^\times,
 \qquad A=(R,+).
\]

Let `Q x Q` act on `A` by left and right multiplication, with either
inverse convention.  Then every nonzero additive character of `A` has an
infinite `Q x Q` orbit.  Equivalently, the only finite orbit in the
Pontryagin dual `dual(A)` is the trivial character.

This closes the finite-orbit gate in the atomic-Hellinger program.  It does
not by itself prove nonhyperlinearity: a normalized-Hilbert--Schmidt
microstate only gives compatible character data on increasing finite root
windows.  Turning those local windows into one global finite atomic
`Q x Q`-set remains an equivariant normalizer-recovery theorem.

## 2. Units additively span the ring

In fact the unit-span statement does not require characteristic two and
does not require passing to a matrix presentation.  For a binary Leavitt
family, every off-diagonal corner

\[
 x=s_iat_j\qquad(i\ne j)
\]

has square zero.  Hence `1+x` is a unit and `x=(1+x)-1` is in the additive
span of the units.  A diagonal corner is a product of two square-zero
off-diagonal corners.  If `x^2=y^2=0`, then

\[
 xy=(1+x)(1+y)-1-x-y,                                  \tag{DOR1}
\]

so it too lies in the unit span.  Finally

\[
 a=(s_0t_0+s_1t_1)a(s_0t_0+s_1t_1)                   \tag{DOR2}
\]

is the sum of its four corners.  Therefore, over every coefficient ring
carrying a binary Leavitt family,

\[
 \operatorname{span}_{\mathbb Z}(R^\times)=R.          \tag{DOR3}
\]

This stronger proof is formalized in
`GroupApproximation/Leavitt/UnitAdditiveSpan.lean`.

The finite-orbit conclusion itself is now formalized in
`GroupApproximation/Leavitt/FiniteDualOrbit.lean`.  The Lean statement avoids
any choice of bases or dimension calculation: a finite family of additive
`F_2`-characters that is closed under every left-unit translate has a common
kernel which is a left ideal.  The quotient embeds in the finite simultaneous
evaluation space, hence is a finite Leavitt module and must be trivial.  In
particular every character in the family is zero.

For comparison, the same fact is visible in the three-leaf prefix
equivalence `R ~= M_3(R)`.  For `i != j`,
the off-diagonal matrix unit satisfies

\[
 E_{ij}(a)=(I+E_{ij}(a))-I,
\]

and both terms on the right are units.  For a diagonal matrix unit, put

\[
 U=(I+E_{ij}(a))(I+E_{ji}(1)).
\]

Then `U` is a unit and

\[
 U=I+E_{ij}(a)+E_{ji}(1)+E_{ii}(a).
\]

This gives the same conclusion in the concrete atlas coordinates.

## 3. No nonzero finite dual orbit

Let `ell:R->F_2` be nonzero and suppose its left--right unit orbit is
finite.  Its linear span `W` in the algebraic dual is finite-dimensional.
For `b in R`, define

\[
 T(b)(a)=\ell(ab).                                     \tag{DOR4}
\]

By `(DOR3)`, write `b` as a finite sum of units.  Equation `(DOR4)` is then
a sum of right-unit translates of `ell`, so `T(b) in W`.  Hence the
bilinear form

\[
 b_\ell(a,b)=\ell(ab)                                  \tag{DOR5}
\]

has finite rank.

Its left radical

\[
 L_\ell=\{a:\ell(ab)=0\text{ for every }b\}
\]

is a right ideal.  It is proper: choose `c` with `ell(c)=1`, so `1` is not
in `L_ell`.  Finite rank would therefore make `R/L_ell` a nonzero
finite-dimensional unital right `R`-module.

No such module exists.  On a right module `V`, the binary Leavitt relations
give inverse maps

\[
 \begin{aligned}
 V&\longrightarrow V\oplus V,&
 x&\longmapsto(xs_0,xs_1),\\
 V\oplus V&\longrightarrow V,&
 (y_0,y_1)&\longmapsto y_0t_0+y_1t_1.
 \end{aligned}                                         \tag{DOR6}
\]

Thus `V` is isomorphic to `V directSum V`, contradicting finite positive
dimension.  This contradiction proves the orbit theorem.

The same proof works for every nonzero functional; the earlier restriction
`ell(1)=1` is unnecessary.  Nonzeroness alone makes the radical proper.

## 4. Exact finite-dimensional consequence

Form the explicit semidirect product

\[
 H=A\rtimes(Q\times Q).                                \tag{DOR7}
\]

In a finite-dimensional unitary representation of `H`, the restriction to
the elementary abelian group `A` is a finite direct sum of characters.
Conjugation by `Q x Q` permutes the finitely many character types occurring
with nonzero multiplicity.  Each such character consequently has a finite
orbit.  The orbit theorem says that every one is trivial.  Therefore

\[
 \boxed{\text{every finite-dimensional unitary representation of }H
        \text{ kills }A.}                              \tag{DOR8}
\]

The group is countable and finitely generated.  Indeed, `Q` is finitely
generated, while `(DOR3)` says that the additive normal closure of `1 in A`
under `Q x Q` is all of `A`.  The existing Leavitt rank equivalence and
property-`(T)` theorem identify `Q` with the rank-three elementary group and
give property `(T)` to `Q x Q`.

## 5. Exact remaining analytic gate

If an HS microstate for `H` could be replaced, without losing covariance,
by one honest finite-dimensional representation of the whole amenable root
`A`, then `(DOR8)` would force the root generator to be trivial, contrary to
its regular trace.  On each fixed finite subgroup of `A`, finite-group
rounding and Fourier Parseval already give this conclusion with
dimension-free constants.

The unresolved quantifier is global.  A character occurring at matrix
coordinate `n` can be extended from the tested root window to `A`, but the
extension need not make the quotient unitaries act on one common finite set
of global characters.  The window required to distinguish the resulting
finite support may depend on that same support.  Diffuse Haar measure in the
exact regular representation shows why weak convergence on every fixed
window cannot be upgraded formally to counting-space Hellinger convergence.

Thus `(DOR8)` supplies an especially small conditional endpoint:

> **Leavitt equivariant character completion.**  A regular-trace HS
> microstate for `A semidirect (Q x Q)` can be perturbed, on each prescribed
> finite set, to a finite atomic character model on which the prescribed
> generators of `Q x Q` act coherently.

This theorem would make `H` explicitly nonhyperlinear.  It is a special
abelian-normalizer recovery statement, not the general tracial commutant
recovery problem.  The orbit calculation above proves that no finite-orbit
escape remains once such a common model has been recovered.

## 6. Two scope checks

The finite-orbit theorem cannot be applied directly to the spectral measure
in an arbitrary tracial representation.  The compact dual of `A` carries
its diffuse Haar probability measure, and every automorphism coming from
`Q x Q` preserves that measure.  Thus absence of nonzero *finite* orbits
does not imply absence of invariant diffuse character models.  Any proof
which silently replaces weak convergence on fixed root windows by
total-variation or Hellinger convergence on one global finite character set
is assuming the completion theorem above.

There is also no automatic extension-permanence shortcut in the needed
direction.  The standard hyperlinear extension theorem applies when the
normal subgroup is hyperlinear and the quotient is amenable.  Here the
normal subgroup `A` is amenable and the quotient `Q x Q` is the hard
nonsofic group, so that theorem does not apply.  Since `Q x Q` embeds in
`H`, proving `H` hyperlinear would itself produce a hyperlinear nonsofic
group; proving it nonhyperlinear requires the missing stability/completion
input rather than the exact finite-representation theorem alone.
