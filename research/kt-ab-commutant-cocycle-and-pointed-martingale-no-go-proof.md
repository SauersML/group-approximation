---
rg: 2
id: kt-ab-commutant-cocycle-and-pointed-martingale-no-go-proof
kind: route
title: Compute the Kun--Thom commutant cocycle and exhibit a pointed first-difference wall
target: kt-ab-compressors-have-one-backward-commutant-edge
requires:
  - kt-two-positive-compressors-generate-full-obstruction
  - kun-thom-single-compressor-sofic-joint-nonsofic
  - kt-single-compressor-canonical-lamps-do-not-exactify-actor
---

# The exact commutant calculation

Write `u_g=sigma(g)`. If `g Gamma g^(-1) subset Gamma` and
`x in R`, then for every `gamma in Gamma`,

~~~text
[u_g^* x u_g,u_gamma]
 =u_g^* [x,u_(g gamma g^(-1))] u_g
 =0.
~~~

Therefore `Phi_g=Ad(u_g^*)` maps `R` into itself. It is a
normal unital trace-preserving injective endomorphism. Direct conjugation
also gives the exact range formula

~~~text
Phi_g(R)=u_g^* R u_g
        =sigma(g^(-1) Gamma g)' intersect M.             (1)
~~~

The cyclic permutation `C` normalizes `Gamma`, so
`Theta=Phi_C` is an automorphism of `R` and `Theta^3=id`.
The assignment `g |-> Phi_g` reverses products:

~~~text
Phi_(g h)=Phi_h o Phi_g.                                 (2)
~~~

Since `A=C B`, equations (1) and (2) give

~~~text
Phi_A=Phi_B o Theta.                                     (3)
~~~

More concretely,

~~~text
A^(-1) Gamma A
 =B^(-1) C^(-1) Gamma C B
 =B^(-1) Gamma B.                                        (4)
~~~

Equations (1) and (4) prove the range equality in (KCE1).

Let `S=Phi_B(R)=Phi_A(R)`. A von Neumann subalgebra of a finite
tracial algebra has a unique trace-preserving conditional expectation, so
both first-edge expectations are the same map `E_S`. In particular,

~~~text
||x-E_A(x)||_2^2+||x-E_B(x)||_2^2
   =2||x-E_S(x)||_2^2.                                   (5)
~~~

This is an identity, not a two-direction Pythagorean estimate. At longer
words, all branching comes from the positions of `Theta` among copies of
`Phi_B`. Thus later holonomy may carry information, but the two length-one
ranges carry only one martingale difference.

For completeness, associate to an endomorphism `Phi` the correspondence
whose Hilbert space is `L^2(R)`, whose right action is the usual one, and
whose left action is

~~~text
x xi = Phi(x) xi.
~~~

Equation (3) says exactly that the left label of the
`A`-correspondence is obtained from the `B`-correspondence by
precomposing with `Theta`. It does not assert that this source twist is
inner. Proving that the twist becomes harmless on one pointed multiplicity
vector is the unresolved cohomological problem.

# The pointed Hilbert--Schmidt identity

Let `x_n` be contractions and put

~~~text
V_n=u_(A,n),       W_n=u_(C,n)u_(B,n).
~~~

For any unitaries `V,W` and contraction `x`,

~~~text
||V^*xV-W^*xW||_2
 <=||V^*x(V-W)||_2+||(V^*-W^*)xW||_2
 <=2||V-W||_2.                                           (6)
~~~

Apply (6) to `V_n,W_n,x_n`. The multiplication row
`A=C B` makes the right side tend to zero and proves (KCE4).
This is exactly where the operator-norm bound on the chosen vector is useful:
it transports that vector through the cocycle, but supplies no estimate
toward the common range `S`.

# A genuine matrix-ultraproduct first-difference wall

Let `V=<Gamma,B>` and `X=V/Gamma`. By
`kun-thom-single-compressor-sofic-joint-nonsofic` the action
`V action X` is sofic. The actor `V` is a subgroup of the residually
finite Kun--Thom actor and is sofic. Wreath permanence therefore makes

~~~text
W_B=(direct_sum_X C_2) rtimes V
~~~

sofic; this is also the model used in
`kt-single-compressor-canonical-lamps-do-not-exactify-actor`.
Its canonical permutation approximations give a trace-preserving embedding
of `L(W_B)` into a matrix tracial ultraproduct. Work in that
ultraproduct and retain the notation `u_g` for actor unitaries.

For `x in X` let `z_x` be the lamp involution at `x`. Put

~~~text
p=(1+z_Gamma)/2.
~~~

Every element of `Gamma` fixes the root coset, hence `p in R`.
Strict compression gives

~~~text
Gamma properly contained in B^(-1) Gamma B.
~~~

Choose `h in B^(-1) Gamma B setminus Gamma`. Then
`h Gamma != Gamma` and

~~~text
u_h p u_h^*=(1+z_(h Gamma))/2.
~~~

Distinct canonical lamps are orthogonal group elements in `L(W_B)`, so

~~~text
||[p,u_h]||_2
 =||p-u_h p u_h^*||_2
 =(1/2)||z_Gamma-z_(h Gamma)||_2
 =1/sqrt(2).                                             (7)
~~~

By (1),

~~~text
Phi_B(R)=sigma(B^(-1) Gamma B)' intersect M,
~~~

so every `y in Phi_B(R)` commutes with `u_h`. Therefore

~~~text
1/sqrt(2)
 =||[p-y,u_h]||_2
 <=2||p-y||_2.                                           (8)
~~~

Taking the infimum over `y` proves (KCE5). Notice that `p` is
an operator-norm-one projection and has exactly zero `Gamma`-adjoint
energy. Property (T) has already rounded it as far as possible: into
`R`. It says nothing about the strictly smaller algebra
`Phi_B(R)`.

# Exact boundary

The preceding model is an unconditional matrix-ultraproduct counterexample
to any proposed lemma whose inputs are only:

1. property (T) of `Gamma`;
2. one strict compressor endomorphism;
3. exact or asymptotic covariance;
4. canonical trace moments; and
5. an operator-norm bound on the chosen vector.

For the full pair, equation (3) shows that the only genuinely new datum is
the cyclic source transport `Theta` and its noncommuting iterates with
`Phi_B`. Extending the pointed one-compressor wall through those
relations would be a hyperlinear model of the forbidden joint wreath.
Forcing it to vanish would solve the desired special centralizer
normalization. Neither conclusion follows from the one-range calculation,
so the root is kept open.

Cross-links:

- `kt-two-positive-compressors-generate-full-obstruction` identifies the
  global `Theta`-holonomy as the full actor obstruction.
- `strict-compressor-mixed-return-collapses-shared-pauli-sign` isolates a
  sufficient named mixed-return estimate; (5) explains why the `A`-edge
  cannot supply that estimate merely as a second root expectation.
- `kt-regular-mask-removes-trace-faithfulness-from-commutant-wall`
  shows why trace-faithfulness cannot eliminate the pointed multiplicity
  vector.
