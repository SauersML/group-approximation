---
rg: 2
id: stw07-separating-qd-quotients-proof
kind: route
title: Take finite direct sums of quotient models chosen to recover the norm on each finite set
target: stw07-separating-qd-quotients-force-quasidiagonality
requires:
  - tww-gabe-schafhauser-af-embedding-theorem
  - gabe-traceless-exact-qd-af-embedding
---

We use Voiculescu's local characterisation of quasidiagonality.  A separable
`A` is quasidiagonal iff for every finite `F ⊆ A` and `ε > 0` there is a
c.c.p. map `φ: A -> M_n` with `||φ(ab) - φ(a)φ(b)|| < ε` and
`||φ(a)|| > ||a|| - ε` for all `a, b ∈ F` (Brown--Ozawa, *C\*-algebras and
finite-dimensional approximations*, Chapter 7).

**Main statement.**  The map `a -> (q_i(a))_i` into `∏_i A/J_i` is an
injective \*-homomorphism, since its kernel is `∩ J_i = 0`.  So it is
isometric: `||a|| = sup_i ||q_i(a)||`.  Given `F` and `ε`, choose a finite set
`S` of indices with `max_(i∈S) ||q_i(a)|| > ||a|| - ε` for every `a ∈ F`.  For
`i ∈ S`, quasidiagonality of `A/J_i` gives a c.c.p. `ψ_i: A/J_i -> M_(n_i)`
with multiplicativity defect `< ε` on `q_i(F)` and `||ψ_i(q_i(a))|| >
||q_i(a)|| - ε` there.  Put `φ = ⊕_(i∈S) ψ_i ∘ q_i`.  It is c.c.p., its
defect on `F` is the maximum of the coordinate defects, so `< ε`, and
`||φ(a)|| = max_(i∈S) ||ψ_i(q_i(a))|| > ||a|| - 2ε`.  Hence `A` is
quasidiagonal.

**1. Radical.**  The ideals `J/R_qd(A)` of `A/R_qd(A)`, over all `J` with
`A/J` quasidiagonal, intersect in `0`.  Their quotients
`(A/R_qd(A))/(J/R_qd(A)) ≅ A/J` are quasidiagonal.  Apply the main statement.

**2. C(X)-algebras.**  Let `θ: C(X) -> Z(M(A))` be the unital structure map
and `π` an irreducible representation of `A`.  Extend `π` to `M(A)`.  By
Schur's lemma `π(θ(C(X)))` consists of scalars, so `π ∘ θ` is a unital
character, that is, evaluation at some `x ∈ X`.  Then
`π(θ(f)a) = f(x)π(a) = 0` for `f ∈ C_0(X\{x})`, so `π` vanishes on the closed
ideal `C_0(X\{x})A` and factors through `A_x`.  Irreducible representations
separate the points of `A`, so `∩_x C_0(X\{x})A = 0`.  Apply the main
statement to the fibres.

**3. Blackadar--Kirchberg.**  Residually finite-dimensional algebras have a
separating family of finite-dimensional, hence quasidiagonal, quotients.
A separable nuclear UCT algebra with a faithful tracial state is
quasidiagonal (`tww-gabe-schafhauser-af-embedding-theorem`).  A separable
exact stably finite traceless algebra is quasidiagonal
(`gabe-traceless-exact-qd-af-embedding`).  In each case the main statement
makes the algebra quasidiagonal, so it is not a counterexample.  For the last
assertion: `E/J_tau` is separable and nuclear with a faithful trace.  If it
satisfies the UCT it is quasidiagonal, so `J_tau` is among the ideals
intersected in `R_qd(E)`.

**Examples showing the asymmetry.**  `C_0((0,1], O_2)` is quasidiagonal
(Voiculescu: cones are quasidiagonal) with non-quasidiagonal quotient `O_2`.
`C([0,1], O_2)` is the sum of the quasidiagonal ideals `C_0([0,2/3), O_2)` and
`C_0((1/3,1], O_2)` (both are subalgebras of cones after reparametrising), but
it contains `O_2` and is not quasidiagonal.
