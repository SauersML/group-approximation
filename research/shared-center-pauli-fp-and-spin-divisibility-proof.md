---
rg: 2
id: shared-center-pauli-fp-and-spin-divisibility-proof
kind: route
title: Quotient the Pauli tape to the Boolean wreath and compute its negative-center spin factor
target: shared-center-pauli-tape-has-same-fp-gate
requires:
  - augmentation-lamp-finite-presentation-criterion
  - property-t-does-not-kill-boolean-fiber-holonomy
---

## 1. Necessity of the Boolean finite-presentation conditions

Quotient `P_X` by the single central relator `J=1`.  Equations (SCP1)
and (SCP2) become two commuting involutions at every site, with all
different sites commuting.  Therefore

~~~text
P_X/<J> congruent_to
 (direct_sum_X (C_2 times C_2)) semidirect A.            (SPS1)
~~~

If `P_X` is finitely presented, the quotient by one additional relator is
finitely presented.  Cornulier's finite-presentation theorem for
permutational wreath products, applied to the nontrivial finitely presented
lamp `C_2 times C_2`, says that (SPS1) is finitely presented only if

~~~text
A is finitely presented,
H is finitely generated,
the diagonal A-action on X times X has finitely many orbits. (SPS2)
~~~

For `X=A/H`, the diagonal orbits are indexed by the double cosets
`H\A/H`.  This proves the forward implication of (SCP3).  In particular,
a shared central extension cannot conceal a non-finitely-presented actor:
killing `J` and the two root lamps is a finite-relator quotient equal to
`A`.

## 2. A finite presentation when the three conditions hold

Conversely, write

~~~text
A=<S | R>,             H=<T>,                           (SPS3)
~~~

where `S,R,T` are finite, and choose representatives
`g_1,...,g_q` of the nontrivial double cosets.  Use generators
`S,X,Z,J` and impose:

~~~text
R,
X^2=Z^2=J^2=1,
[J,X]=[J,Z]=[J,s]=1                         (s in S),
[X,Z]=J,
[X,t]=[Z,t]=1                              (t in T),
[u,g_i v g_i^(-1)]=1
       (1<=i<=q, u,v in {X,Z}).                         (SPS4)
~~~

These are finitely many relators.

Let `X_(aH)=aXa^(-1)` and `Z_(aH)=aZa^(-1)`.
The stabilizer relations make these definitions independent of the coset
representative.  If `aH!=bH`, write

~~~text
a^(-1)b=h_1 g_i h_2,             h_1,h_2 in H.          (SPS5)
~~~

The stabilizer relations remove `h_2` from the second root lamp and
`h_1` from the first after conjugating the commutator.  The last line of
(SPS4) then gives all four cross-site commutators in (SCP2).  Conjugating
the local relation gives `[X_x,Z_x]=J` at every site.

Thus (SPS4) is the usual infinite presentation of `E_X semidirect A` after
Tietze-eliminating every nonroot site generator.  It presents `P_X` and
proves the reverse implication of (SCP3).

For a sharply two-transitive action there are exactly two diagonal pair
orbits, hence exactly one nontrivial double coset in (SPS4).  The only
remaining presentation hypotheses are finite presentation of `A` and
finite generation of `H`.

## 3. The sign survives algebraically

For every finite `F subset X`, put one copy of `C^2` at each site.  Let
`X_x,Z_x` act as the two Pauli involutions on the `x` factor and as the
identity elsewhere, and let `J=-I`.  These actions are compatible as
`F` grows.  On the incomplete infinite tensor product with the standard
reference vector, every finite-support Pauli word is a well-defined unitary,
and permutations of `X` are implemented by tensor-factor permutations.
This gives a unitary representation of `P_X` with

~~~text
J |-> -I.                                                (SPS6)
~~~

Hence the marked sign is nontrivial in the presented group.

## 4. Exact spin divisibility

Let `rho` be any unitary representation and let `K_-` be the negative
spectral subspace of the central involution `rho(J)`.  It is invariant
under the whole group.  Fix distinct sites
`F={x_1,...,x_m}`.  On `K_-`, the operators

~~~text
rho(X_(x_i)), rho(Z_(x_i))                               (SPS7)
~~~

are Pauli pairs at the same site and commute between different sites.
The complex star-algebra they generate is the tensor product of `m`
copies of `M_2(C)`:

~~~text
Alg(SPS7) congruent_to M_(2^m)(C).                       (SPS8)
~~~

Every finite-dimensional representation of a full matrix algebra is a
multiple of its defining representation.  Therefore

~~~text
K_- congruent_to (C^2)^(tensor m) tensor C^(r_F),
dim(K_-)=2^m r_F.                                        (SPS9)
~~~

If the original representation is finite-dimensional and `X` is
infinite, (SPS9) holds for arbitrarily large `m`.  The fixed integer
`dim(K_-)` is divisible by every `2^m`, hence it is zero.  Thus every
finite-dimensional exact representation sends `J` to `+I`.

Equation (SPS9) is also the precise finite-window decomposition in the
claim.  Suppose an actor element sends `F` to `gF`.  On the spin factors
there is a canonical tensor relabeling implementing

~~~text
X_x |-> X_(gx),             Z_x |-> Z_(gx).              (SPS10)
~~~

Any two implementers of (SPS10) differ by a unitary in the commutant of the
full matrix algebra (SPS8), namely by a unitary on `C^(r_F)`.  Composition
of actor arrows imposes exactly the corresponding unitary cocycle law on
these multiplicity maps.  No additive cocycle is present, so property
`(T)` alone does not remove them.

## 5. The logarithmic seam

Let a negative-center matrix corner have dimension `D_F`.  From (SPS9),

~~~text
r_F=D_F/2^m.                                             (SPS11)
~~~

For fixed `m`, any positive-density corner in a matrix sequence whose
ranks tend to infinity has `r_F->infinity`.  Conversely,
`r_F<=K` implies

~~~text
m>=log_2(D_F)-log_2(K).                                  (SPS12)
~~~

This divisibility is exact and survives normalized corner trace: replacing
the ambient trace by the corner trace changes neither the integer identity
(SPS9) nor the multiplicity ratio (SPS11).

Finite bi-index reduces (SPS4) to finitely many prototype relators, but an
approximate representation controls a remote conjugate through a chosen
transporter word.  The word lengths of transporters and stabilizer
comparisons are unbounded on an infinite orbit.  Fixed-presentation
hyperlinear convergence gives no estimate when the packet size grows at
(SPS12).  A uniform property-`(T)` site-coherence theorem could change
this conclusion, but it is not a consequence of the algebraic
finite-presentation calculation above.
