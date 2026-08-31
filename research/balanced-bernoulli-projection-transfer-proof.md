---
rg: 2
id: balanced-bernoulli-projection-transfer-proof
kind: route
title: Linearize a commutant unitary and identify the Bernoulli obstruction
target: fdt7-is-balanced-bernoulli-projection-transfer
requires:
  - kt-ccr-holds-on-the-fd-tempered-adjoint-sector
  - fd-invisibility-of-compression
  - coset-bernoulli-ce-refutes-relative-commutant-collapse
---

## Step 1: the two-by-two linearization is isometric

For `v in U(d)` put

~~~text
J=[[0,v],[v^*,0]],       P=(I+J)/2.
~~~

Direct multiplication gives `J^*=J` and `J^2=I`.  Its diagonal blocks
vanish, so `Tr(J)=0`.  Therefore the eigenvalues `+1` and `-1` each
have multiplicity `d`, and `P` is a rank-`d` projection in `M_(2d)`.

For `U_tilde=diag(U,U)`,

~~~text
[U_tilde,J]
 =[[0,Uv-vU],[Uv^*-v^*U,0]].                            (BBQ1)
~~~

The two off-diagonal blocks have the same Hilbert--Schmidt norm, because

~~~text
[v^*,U]=-v^*[v,U]v^*.
~~~

After division by the doubled matrix dimension, `(BBQ1)` gives

~~~text
||[U_tilde,J]||_(2,2d)^2=||[U,v]||_(2,d)^2.             (BBQ2)
~~~

Also,

~~~text
U_tilde P U_tilde^*-P
 =(1/2)(U_tilde J U_tilde^*-J),
~~~

and right multiplication by `U_tilde` is isometric.  This proves
`(BBP2)`.

If `pi` is a tuple of actor unitaries, replacing every entry by its doubled
diagonal repeats every relator defect in two identical blocks.  Its
normalized `2`-norm and normalized trace are unchanged.  Hence no actor
accuracy is lost by the linearization.

## Step 2: equivalence with balanced projection transfer

Start with a sequence `v_n` in FDT7 and use Step 1.  For every actor
generator `g`,

~~~text
||pi_n(g)~ P(v_n) pi_n(g)~^*-P(v_n)||_2
 =(1/2)||[pi_n(g),v_n]||_2.                              (BBQ3)
~~~

Thus a unitary refuter produces a trace-half projection refuter in doubled
dimension with the same actor microstate.

Conversely, given projections `p_n` satisfying `(BBP3)`, define

~~~text
v_n=2p_n-I.
~~~

These are self-adjoint unitaries and

~~~text
||[pi_n(g),v_n]||_2
 =2||pi_n(g)p_n pi_n(g)^*-p_n||_2.                       (BBQ4)
~~~

Therefore the unitary and balanced-projection forms are equivalent up to the
fixed factor two.  If an unbalanced projection arises first, replace it by
`p direct_sum (I-p)`; this has normalized trace `1/2` and exactly the same
conjugation displacement after diagonal doubling.

This is why polar and spectral methods stop here.  There is no approximate
partial isometry or fuzzy spectral cut left to repair: `p_n` is already an
exact projection of macroscopic rank.

## Step 3: the exact Bernoulli profile

Let `X=G/Lambda` and let
`Omega={+1,-1}^X` with product measure.  Write `z_x` for the coordinate
sign.  The family satisfies

~~~text
z_x=z_x^*=z_x^(-1),
tau(z_x)=0,
tau(z_x z_y)=0 for x!=y.                                (BBQ5)
~~~

Let `G` act by translation and let
`N=L^infinity(Omega) crossed_product G`.  For
`o=Lambda` set

~~~text
v=z_o,       p=(1+v)/2.
~~~

If `lambda in Lambda`, then `lambda o=o`, so
`u_lambda p u_lambda^*=p`.  If `gamma notin Lambda`, then
`gamma o!=o` and `(BBQ5)` gives

~~~text
||u_gamma p u_gamma^*-p||_2^2
 =(1/4)||z_(gamma o)-z_o||_2^2
 =(1/4)(2-2tau(z_(gamma o)z_o))
 =1/2.                                                    (BBQ6)
~~~

This proves `(BBP4)`.  The vectors `z_(g o)` are an orthonormal family and

~~~text
Ad(u_h)z_(g o)=z_(hg o).
~~~

Their closed span is therefore the quasi-regular representation
`ell^2(G/Lambda)`, with `z_o` corresponding to the base coset vector.

For the Kun--Thom pair, suppose this quasi-regular representation were weakly
contained in `pi_FD`.  The base vector is `Lambda`-fixed, so
`kt-ccr-holds-on-the-fd-tempered-adjoint-sector` would make it
`Gamma`-fixed, contradicting `(BBQ6)`.  Hence the Bernoulli counterprofile
lies exactly in the non-FD-tempered sector isolated there.

The construction uses no approximation and works in a finite tracial von
Neumann algebra for every proper subgroup.  Its matrix boundary can be
stated exactly.  Let

~~~text
A=direct_sum_(G/Lambda) C_2,       W=A semidirect G,      (BBQ6b)
~~~

with the coordinate-permutation action.  Pontryagin duality identifies
`L(A)` with `L^infinity(Omega)`, intertwines the two `G`-actions, and
therefore gives the trace-preserving isomorphism

~~~text
L(W)=L(A semidirect G)
    congruent_to L^infinity(Omega) crossed_product G=N.  (BBQ6c)
~~~

A countable group is hyperlinear exactly when its group von Neumann algebra
has a trace-preserving embedding into a tracial matrix ultraproduct.
Therefore this Bernoulli profile has such a realization exactly when `W`
is hyperlinear.  If it does, restrict the embedding of `L(W)` to the
canonical `G`-unitaries.  Their trace is the canonical group trace, so this
is a trace-faithful actor microstate.  The embedded base-coordinate
projection `p` is `Lambda`-central and, by `(BBQ6)`, is moved a fixed
distance by `gamma`.  It is then an actual counterexample to `(BBP3)`,
FDT7, and (CCR).

No closure theorem used in the Kun--Thom route constructs a hyperlinear model
of this generalized coset wreath product from the available actor
microstates.  Thus `(BBQ6b)` is a conditional refuter, not a refutation.
It follows unconditionally that property `(T)`, conditional expectations,
projection rank `1/2`, and abstract finite-factor inequalities cannot alone
imply `(BBP3)`.  The exact missing input is hyperlinearity of `W`, or
equivalently matrix embeddability of `N`.

## Step 4: projective tensoring erases scalar displacement

Let

~~~text
X=[[0,1],[1,0]],       Z=[[1,0],[0,-1]].
~~~

Then `XZ=-ZX`.  Hence

~~~text
[X,Z]=2XZ,       ||[X,Z]||_2=2.                          (BBQ7)
~~~

On the other hand, scalar commutators disappear under the adjoint and
conjugate-tensor functors:

~~~text
Ad(X)Ad(Z)=Ad(XZ)=Ad(-ZX)=Ad(Z)Ad(X),
(X tensor conjugate(X))(Z tensor conjugate(Z))
 =(Z tensor conjugate(Z))(X tensor conjugate(X)).        (BBQ8)
~~~

Thus the maximal phase-sensitive defect in `(BBQ7)` becomes zero.  Tensoring
the witness with its inverse or passing to inner superoperators may be useful
for projective commutant transfer, but it cannot prove the ordinary
commutant statement FDT7.

The linearization of Step 1 has the opposite virtue: it retains scalar phase
exactly.  Its price is that it produces the Bernoulli half-projection rather
than an exact actor representation.

## Step 5: corner Ulam stabilization would already prove FDT7

Suppose a proposed stabilization starts from `pi_n,p_n` in `(BBP3)` and
returns genuine finite-dimensional representations `rho_n:G->U(D_n)`
and projections `q_n` such that

~~~text
[q_n,rho_n(lambda)]=0 for every lambda in Lambda,
||p_n-q_n||_2 ->0,
||pi_n(gamma)-rho_n(gamma)||_2 ->0.                      (BBQ9)
~~~

Padding may be included provided all norms are taken on the common padded
space and its relative size tends to one.

By `fd-invisibility-of-compression`,

~~~text
rho_n(Lambda)=rho_n(Gamma).
~~~

Therefore `q_n` commutes with `rho_n(gamma)`.  Insert
`rho_n(gamma)q_n rho_n(gamma)^*=q_n` and use the triangle inequality:

~~~text
||pi_n(gamma)p_n pi_n(gamma)^*-p_n||_2
 <=2||p_n-q_n||_2
   +2||pi_n(gamma)-rho_n(gamma)||_2.                    (BBQ10)
~~~

The right side tends to zero, proving `(BBP3)` and hence FDT7.

The algebra generated by `2p_n-I` is only the two-point algebra `C^2`.
Accordingly, an alleged shortcut which stabilizes the actor covariance on
the C-star algebra generated by the witness still has to produce exactly the
data in `(BBQ9)`.  Once covariance with `gamma` is retained, this is a
source-specific actor/corner exactification theorem, not a consequence of
polar decomposition or amenability of `C^2`.

This proves the claimed boundary: the unitary hypothesis removes thin-corner
escapes by a reversible balanced projection, but it does not cross from
finite tracial Bernoulli models to matrix-ultraproduct models.  FDT7 remains
open.
