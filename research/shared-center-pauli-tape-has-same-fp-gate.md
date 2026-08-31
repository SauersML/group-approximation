---
rg: 2
id: shared-center-pauli-tape-has-same-fp-gate
kind: claim
title: Shared-center Pauli lamps have the Boolean finite-presentation gate and a logarithmic multiplicity seam
distinct_from:
  finite-bi-index-clifford-tape-presentation: that gives a sufficient presentation for one complete-graph Clifford generator and a finite-bi-index pair; this gives an if-and-only-if criterion for two-generator Heisenberg sites and computes the negative-center matrix factor.
  augmentation-lamp-finite-presentation-criterion: that treats the abelian augmentation lamp; this shows that adjoining a shared nonabelian Pauli center does not weaken either actor finiteness requirement.
  sharply-two-transitive-augmentation-lamp-host-audit: that audits the published Andre--Guirardel actor for abelian lamps; this applies the same audit to shared-center Heisenberg lamps and exposes the remaining logarithmic multiplicity.
  moving-tail-fixed-traces-keep-quantum-fibers: that gives an exact same-dimension moving-tail countermodel; this identifies the corresponding multiplicity group inside every negative-center Pauli window.
---

**ESTABLISHED FINITE-PRESENTATION EQUIVALENCE AND LOCAL SPIN
DIVISIBILITY; UNIFORM MOVING-WINDOW SOUNDNESS OPEN.**

Let a group `A` act transitively on an infinite set `X=A/H`.  Define the
shared-center Pauli base `E_X` by involutions

~~~text
J, X_x, Z_x                 (x in X)                    (SCP1)
~~~

with `J` central,

~~~text
[X_x,Z_x]=J,
[X_x,X_y]=[X_x,Z_y]=[Z_x,X_y]=[Z_x,Z_y]=1   (x!=y).     (SCP2)
~~~

The actor permutes the site labels.  Put `P_X=E_X semidirect A`.  Then

~~~text
P_X is finitely presented
iff
A is finitely presented,
H is finitely generated,
and H\A/H is finite.                                   (SCP3)
~~~

Thus a sharply two-transitive action removes the double-coset gate but not
the other two gates.  For the two-generated simple property-`(T)` sharply
two-transitive actor of Andre--Guirardel, neither finite presentability of
the actor nor finite generation of its point stabilizer is supplied by the
published construction.  The shared central sign therefore does not yet
produce a finitely presented host from that actor.

The sign `J` is nontrivial in `P_X`, but every exact finite-dimensional
unitary representation sends `J` to `+I`.  More precisely, on the
`J=-I` sector, any finite window `F subset X` of size `m` generates

~~~text
M_(2^m)(C) tensor I_(r_F).                               (SCP4)
~~~

Consequently every exact negative-center carrier has the divisibility

~~~text
D_F=2^m r_F.                                             (SCP5)
~~~

An actor normalizer of this finite packet is a canonical tensor-factor
relabeling, up to an arbitrary unitary on the multiplicity space
`C^(r_F)`.  Actor products constrain those unitaries as a cocycle; property
`(T)` does not make an exact multiplicity representation scalar or
monomial.

In a fixed-window tracial matrix sequence, every nonzero full
negative-center corner therefore has `r_F->infinity`.  Bounded
multiplicity `r_F<=K` requires

~~~text
m>=log_2(D_F)-log_2(K).                                  (SCP6)
~~~

Sharp two-transitivity makes all off-site commutators conjugate to one
prototype and makes the presentation finite when the two actor finiteness
conditions hold.  It does not change (SCP6): transporting a prototype
relation to remote sites uses unbounded transporter/stabilizer words, while
hyperlinear convergence controls only each fixed finite word set.  Hence
shared-center Pauli divisibility is a capacity theorem, not yet a
finitely-presented asymptotic obstruction.

DERIVATION
shared-center-pauli-fp-and-spin-divisibility-proof
