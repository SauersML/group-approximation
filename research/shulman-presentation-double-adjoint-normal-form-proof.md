---
rg: 2
id: shulman-presentation-double-adjoint-normal-form-proof
kind: route
title: Specialize Shulman's Julia lift to a free vertex and identify the left-right action
target: shulman-presentation-double-witnesses-have-adjoint-normal-form
requires:
  - symmetric-double-weak-mf
  - simple-map-quotient-has-rigid-fd-restriction
---

Put `A=C*(F)` and `C=C*(K)`.  In the proof of Shulman's symmetric-amalgam
theorem, start from a faithful representation

```text
pi=pi_1 * pi_2 : A *_C A -> B(H)
```

and set

```text
rho_1=pi_1 directSum pi_2,
rho_2=pi_2 directSum pi_1.
```

The block swap `w` satisfies `rho_1=w^* rho_2 w` and commutes with the common
copy of `C`.  Since `F` is free, the finitely many unitary generators of
`rho_2(F)` can be lifted by finite-dimensional unitaries.  The resulting
coordinate maps are exact representations of `F`; no vertex relator or
asymptotic correction is needed.

Shulman's Lemma 9 lifts `diag(w,-w^*)` to a Julia unitary `V_j`, after a
twofold duplication, with operator-norm commutator at most `1/j` on the
first `j` elements of an exhaustion of `C`.  Hence before the final
continuous-section gluing, the two vertex maps are exactly

```text
phi_j^(2)=phi_j directSum phi_j,
phi_j^(1)=V_j^* phi_j^(2) V_j.                         (SJAP1)
```

Evaluate `(SJAP1)` at an inner matrix coordinate.  This gives exact
representations `sigma_(j,m)` of `F` and exact unitaries `V_(j,m)`, in
dimension four times the inner coordinate, and the edge estimate is uniform
in `m`.  The faithful stabilized quotient representation sends the reduced
fold word

```text
i_1(f_0)i_2(f_0)^(-1)
```

away from one.  Strong-star convergence of the inner coordinates therefore
gives arbitrarily late `m` on which its operator norm is bounded below by a
fixed positive constant.  Choose one such `m=m(j)` diagonally.  With

```text
v_j=sigma_j,
u_j=V_j^* sigma_j V_j,
```

the edge commutators tend to zero pointwise on `K` and the `f_0` commutator
stays operator-norm visible.  This proves `(SJA1)--(SJA2)`.

Now define the Hilbert--Schmidt unitary `L_(V_j):T |-> V_jT`.  Direct
calculation gives

```text
L_(V_j)(u_j(f)T v_j(f)^*)
 =sigma_j(f)(V_jT)sigma_j(f)^*,
```

which is `(SJA3)`.

It remains to identify the zero-energy sector.  Its fixed space is
`sigma_j(K)'`.  If `Z` is a unitary in this commutant, the two
representations `sigma_j` and `Z sigma_j Z^*` agree on `K`.  The restriction
rigidity theorem makes them agree on all of `F`, so `Z in sigma_j(F)'`.
The unitaries span the finite-dimensional C-star algebra `sigma_j(K)'`;
hence `sigma_j(K)'=sigma_j(F)'`, proving `(SJA4)`.

Finally, the source proof controls the Julia commutator only in operator
norm.  Adding a common exact summand to `sigma_j` and the identity summand to
`V_j` preserves every displayed estimate and the separating maximum norm,
but changes all normalized multiplicities arbitrarily.  Such summands may
be placed on inner coordinates escaping every fixed vector and therefore do
not change the strong quotient representation.  No positive-rank conclusion
for a nonzero spectral band follows from the published construction.
