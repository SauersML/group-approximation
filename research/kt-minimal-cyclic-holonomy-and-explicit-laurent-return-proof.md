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

# 2. The cyclic average retains a quantitative wall

Let `X=G/Gamma` and

~~~text
W=(direct_sum_X C_2) rtimes G.
~~~

Write `z_x` for the lamp involution at `x in X` and work in
`M=L(W)` with its canonical trace. Define three root-normalizer lamps and
their average by

~~~text
p_i=(1+z_(C^(-i)Gamma))/2,       i=0,1,2,
q=(p_0+p_1+p_2)/3.
~~~

The stabilizer of `C^(-i)Gamma` is
`C^(-i) Gamma C^i=Gamma`. Hence every `p_i`, and therefore
`q`, belongs to `R`. The map `Theta=Ad(sigma(C)^*)` cycles
the three projections:

~~~text
Theta(p_i)=p_(i+1 mod 3),       Theta(q)=q.               (6)
~~~

Thus `q` is exactly what order-three averaging produces. It is a positive
operator-norm-one contraction.

Strictness gives
`Gamma properly contained in B^(-1) Gamma B`. Use the explicit element
`h` from Section 3 below. Put

~~~text
P={Gamma,C^(-1)Gamma,C^(-2)Gamma}.
~~~

The six cosets in `P disjoint_union hP` are distinct. Indeed the three
cosets in `P` are distinct because their actor components modulo
`Gamma` are `1,C^(-1),C^(-2)`. If

~~~text
h C^(-i)Gamma=C^(-j)Gamma,
~~~

then `C^j h C^(-i)` belongs to `Gamma`. Its actor component forces
`i=j mod 3`, after which this would say that the cyclic Laurent conjugate
`C^i h C^(-i)` lies in `Gamma`, contrary to its Laurent denominator.
The cosets within `hP` are distinct by cancellation.

Now

~~~text
q=1/2+(1/6) sum_(x in P) z_x,
sigma(h)q sigma(h)^*
 =1/2+(1/6) sum_(x in P) z_(h x).
~~~

The six displayed lamp group elements are trace orthogonal, so

~~~text
||[q,sigma(h)]||_2
 =||q-sigma(h)q sigma(h)^*||_2
 =sqrt(6/36)
 =1/sqrt(6).                                             (7)
~~~

Every element of

~~~text
Phi_B(R)=sigma(B^(-1) Gamma B)' intersect M
~~~

commutes with `sigma(h)`. For `a in Phi_B(R)`, (7) gives

~~~text
1/sqrt(6)
 =||[q-a,sigma(h)]||_2
 <=2||q-a||_2.
~~~

Taking the infimum proves

~~~text
dist_2(q,Phi_B(R))>=1/(2 sqrt(6)).                       (8)
~~~

Equations (6) and (8) prove the failure of (KHL4). This is a counterexample
in a finite tracial algebra satisfying the complete actor and wreath
relations, not merely the two displayed endomorphism equations.

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

also lies outside `Gamma`. Equation (6), trace invariance, and the cyclic
symmetry of `q` give

~~~text
||[q,sigma(h_i)]||_2=1/sqrt(6).                          (10)
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
