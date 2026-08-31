---
rg: 2
id: kt-minimal-cyclic-holonomy-and-explicit-laurent-return-proof
kind: route
title: Compute the first cyclic compressor holonomy and its root-lamp return
target: kt-order-three-average-does-not-kill-the-pointed-martingale-wall
requires:
  - kt-ab-compressors-have-one-backward-commutant-edge
  - full-shared-pauli-rows-have-an-exact-finite-tracial-model
  - strict-compressor-mixed-return-collapses-shared-pauli-sign
---

# 1. The smallest cyclic noncommutation

Let

~~~text
x=E_31,       y=E_12,       z=E_32.
~~~

Matrix-unit multiplication gives

~~~text
x y=z,
y x=z x=z y=0.
~~~

Hence

~~~text
(I+x)(I+y)=I+x+y+z
          =(I+z)(I+y)(I+x).                              (1)
~~~

Since `C^(-1)E_12 C=E_31`, equation (1) is exactly

~~~text
B_- B=D B B_-,
B_-=C^(-1) B C,
D=I+E_32.                                                (2)
~~~

All three matrices in (2) have nonnegative entries and determinant one, so
they induce positive injective polynomial-ring compressors of `Gamma`.

For backward commutant maps the product order reverses:

~~~text
Phi_(g k)=Phi_k o Phi_g.                                 (3)
~~~

Also

~~~text
Theta o Phi_B o Theta^(-1)
 =Phi_C o Phi_B o Phi_(C^(-1))
 =Phi_(C^(-1) B C)
 =Phi_(B_-).                                             (4)
~~~

Applying (3) to both sides of (2) gives

~~~text
Phi_B o Phi_(B_-)
 =Phi_(B_-) o Phi_B o Phi_D.                             (5)
~~~

This is the first place where the cyclic source automorphism fails merely
to relabel the common length-one range: the failure is measured by the
third positive root direction `D`. It is the endomorphism form of the
Steinberg commutator `[I+E_31,I+E_12]=I+E_32`.

# 2. The order-three average fixes the obstructing projection

Let `X=G/Gamma` and

~~~text
W=(direct_sum_X C_2) rtimes G.
~~~

Write `z_x` for the lamp involution at `x in X` and work in
`M=L(W)` with its canonical trace. The root projection is

~~~text
p=(1+z_Gamma)/2.
~~~

The stabilizer of the root coset is `Gamma`, so `p` commutes with
`sigma(Gamma)` and belongs to `R`. Moreover `C` normalizes
`Gamma`. Thus `C^(-1)Gamma=Gamma` as a coset and

~~~text
Theta(p)=sigma(C)^* p sigma(C)
        =(1+z_(C^(-1)Gamma))/2
        =p.                                              (6)
~~~

In particular the order-three average

~~~text
(1/3)(p+Theta(p)+Theta^2(p))
~~~

is exactly `p`; it does not change the vector at all.

Strictness gives
`Gamma properly contained in B^(-1) Gamma B`. Choose any
`h in B^(-1) Gamma B setminus Gamma`. Then `hGamma!=Gamma`,
and the two distinct lamp group elements are trace orthogonal. Therefore

~~~text
||[p,sigma(h)]||_2
 =||p-sigma(h)p sigma(h)^*||_2
 =(1/2)||z_Gamma-z_(hGamma)||_2
 =1/sqrt(2).                                             (7)
~~~

Every element of

~~~text
Phi_B(R)=sigma(B^(-1) Gamma B)' intersect M
~~~

commutes with `sigma(h)`. For `q in Phi_B(R)`, (7) gives

~~~text
1/sqrt(2)
 =||[p-q,sigma(h)]||_2
 <=2||p-q||_2.
~~~

Taking the infimum proves

~~~text
dist_2(p,Phi_B(R))>=1/(2 sqrt(2)).                       (8)
~~~

Equations (6) and (8) prove the failure of (KHL4). Notice that this is a
counterexample in a finite tracial algebra satisfying the complete actor and
wreath relations, not merely the two displayed endomorphism equations.

# 3. A fixed elementary Laurent return

For the pinned compressor, exponent columns transform by

~~~text
B(n_1,n_2,n_3)=(n_1+n_2,n_2,n_3).
~~~

The exponent `e_2` is not in `B N^3`, while

~~~text
B^(-1)e_2=(-1,1,0).
~~~

Consequently the elementary matrix

~~~text
gamma=e_12(x_2)
~~~

belongs to `Gamma` but not to `B Gamma B^(-1)`, and

~~~text
h=B^(-1) gamma B=e_12(x_1^(-1)x_2)                       (9)
~~~

belongs to `B^(-1) Gamma B` but not to `Gamma`. Matrix entries detect
the last nonmembership directly: the coefficient `x_1^(-1)x_2` is not
in the polynomial ring. Substitution in (7) proves (KHL6).

Because `C` normalizes `Gamma`, every

~~~text
h_i=C^(-i) h C^i,       i=0,1,2,
~~~

also lies outside `Gamma`. Equation (6) and trace invariance give

~~~text
||[p,sigma(h_i)]||_2=1/sqrt(2).                          (10)
~~~

This three-word packet is the first explicit target for pointed
operator-norm-bounded control.

# 4. What remains matrix-specific

The exact model above rules out every proof assembled only from tracial
positivity, the Gamma Kazhdan inequality, the order-three average, and the
fixed relations (2). It does not rule out a matrix-specific theorem saying
that, in a trace-faithful matrix ultraproduct representation of the pinned
Kun--Thom actor, the full microstate equations force the three quantities
in (10) to vanish for the chosen multiplicity vector.

Such a theorem must use finite-dimensional approximation in an essential
way. Conversely, a matrix-ultraproduct realization retaining one nonzero
quantity in (10), together with the shared-Pauli rows, would provide the
desired countermodel. This is exactly the surviving later-word holonomy
gate.
