---
rg: 2
id: boolean-atom-overlap-coupling-and-diffuse-corner-proof
kind: route
title: Couple Boolean atoms, perform block Procrustes matching, and count full-corner multiplicity
target: boolean-atom-overlap-spatializes-arrows-but-full-corners-stay-diffuse
requires:
  - coset-wreath-wall-survives-full-commutant-corners
  - moving-lamp-refinement-cocycle-has-diffuse-fibers
  - wreath-not-sofic
---

## Step 1: the overlap matrix is a coupling

Put `R_chi=UP_chi U^*`.  For projections `R,Q`,

~~~text
tr(RQ)=tr(QRQ)>=0.                                      (BAP1)
~~~

Therefore `mu(chi,psi)=tr(R_chi Q_psi)` is nonnegative.  Since both
families are PVMs,

~~~text
sum_psi mu(chi,psi)=tr(R_chi),
sum_chi mu(chi,psi)=tr(Q_psi),
sum_(chi,psi) mu(chi,psi)=1.                            (BAP2)
~~~

Thus `mu` is a coupling even though the two PVMs need not commute with one
another.

Write

~~~text
a_j=U v_j U^*=sum_chi chi_j R_chi,
b_j=w_j=sum_psi psi_j Q_psi.                            (BAP3)
~~~

Both are self-adjoint unitaries.  Traciality gives

~~~text
epsilon_j^2
 =tr((a_j-b_j)^2)
 =2-2tr(a_jb_j)
 =4 sum_(chi_j!=psi_j) mu(chi,psi).                     (BAP4)
~~~

Every off-diagonal pair `chi!=psi` differs in at least one coordinate.
The union bound in the coupling `mu` therefore gives

~~~text
eta=sum_(chi!=psi)mu(chi,psi)
 <=sum_j sum_(chi_j!=psi_j)mu(chi,psi)
 =(1/4)sum_j epsilon_j^2.                               (BAP5)
~~~

Finally,

~~~text
sum_chi ||R_chi-Q_chi||_2^2
 =sum_chi (tr(R_chi)+tr(Q_chi)-2tr(R_chiQ_chi))
 =2-2sum_chi mu(chi,chi)
 =2eta.                                                  (BAP6)
~~~

This proves `(BAO3)` and `(BAO4)`.  Unlike a separate telescoping estimate
for every character, `(BAP5)` controls the total wrong-atom mass and has no
factor exponential in the number of atoms.

## Step 2: equal-rank atoms admit a close global block matcher

Assume `rank(R_chi)=rank(Q_chi)` for every `chi`.  Let
`H_chi=R_chi C^d` and `K_chi=Q_chi C^d`.  Among all isometries
`C_chi:H_chi->K_chi`, finite-dimensional Procrustes duality gives

~~~text
max Re Tr(C_chi)=||Q_chi R_chi||_1.                     (BAP7)
~~~

For completeness, choose orthonormal column matrices `E_chi,F_chi` for
`H_chi,K_chi`.  Every such isometry is
`F_chi Z E_chi^*` with `Z` unitary, and

~~~text
Tr(F_chi Z E_chi^*)=Tr(Z E_chi^*F_chi).
~~~

Maximizing its real part gives the nuclear norm of
`E_chi^*F_chi`, whose singular values are those of `Q_chi R_chi`.

Choose a maximizer for each `chi` and take their orthogonal direct sum
`C`.  The domain spaces partition `C^d` and so do the range spaces, hence
`C` is unitary and

~~~text
C R_chi C^*=Q_chi.                                      (BAP8)
~~~

All singular values of `Q_chi R_chi` lie in `[0,1]`, so their sum is at
least the sum of their squares.  Consequently

~~~text
Re tr(C)
 =d^(-1)sum_chi ||Q_chi R_chi||_1
 >=d^(-1)sum_chi ||Q_chi R_chi||_2^2
 =sum_chi tr(R_chiQ_chi)
 =1-eta.                                                 (BAP9)
~~~

It follows that

~~~text
||C-I||_2^2=2-2 Re tr(C)<=2eta.                         (BAP10)
~~~

For `V=CU`, equation `(BAP8)` becomes
`VP_chiV^*=Q_chi` and
`||V-U||_2=||C-I||_2`.  Combining `(BAP5)` and `(BAP10)` proves
`(BAO5)`.

The correction is global, not a collection of incompatible rotations on
overlapping two-plane sums.  That is why the Procrustes direct sum is taken
between the two complete orthogonal decompositions.

## Step 3: rank imbalance costs exactly its total variation

Let `r_chi=rank(P_chi)` and `s_chi=rank(Q_chi)`.  Because their totals
are both `d`, the number of dimensions which must change atom labels is

~~~text
k=(1/2)sum_chi |r_chi-s_chi|=d delta.                   (BAP11)
~~~

Choose `k` basis vectors from the surplus `P`-atoms and reassign them to
the deficit labels.  This produces a PVM `Ptilde_chi` with
`rank(Ptilde_chi)=s_chi`.  Every moved vector is removed from one atom
projection and inserted into one other atom projection.  Hence

~~~text
sum_chi ||Ptilde_chi-P_chi||_2^2=2k/d=2delta.           (BAP12)
~~~

The corresponding commuting signs
`vtilde_j=sum_chi chi_j Ptilde_chi` give a balanced exact Boolean model.
The triangle inequality in the Hilbert direct sum of atom matrices combines
`(BAP12)` with `(BAP6)`.  Thus whenever `eta,delta->0`, balancing followed
by Step 2 changes the original arrow by `o_2(1)`.

For a fixed lamp window in a canonical microstate, Fourier inversion makes
every atom trace tend to `2^(-m)`.  Therefore both endpoint distributions
have `delta->0`.  Pairwise actor arrows can always be made block-spatial
after a vanishing perturbation.  This conclusion does not choose compatible
rank transfers for several arrows at once.

## Step 4: a full corner keeps every fixed Boolean fiber diffuse

Let `B_E` be the finite lamp algebra on `m` sites in the canonical Bernoulli
algebra.  Its character atoms satisfy

~~~text
tau(P_(E,chi))=2^(-m).                                  (BAP13)
~~~

Assume a trace-preserving embedding `Theta:L(W)->M` and choose a nonzero
full relative-commutant projection `e`.  By
`coset-wreath-wall-survives-full-commutant-corners`, the corner map is
trace preserving.  Therefore

~~~text
tau_e(eTheta(P_(E,chi)))=2^(-m).                        (BAP14)
~~~

If `M=product_omega M_(d_n)`, lift `e` to projections `e_n` of ranks
`r_n` and lift the finite PVM in `eMe` to exact PVMs in
`e_nM_(d_n)e_n congruent_to M_(r_n)`.  Finite PVMs lift after an
`o_2(1)` perturbation because the relations of the finite-dimensional
algebra `C^(2^m)` are stable.  Equation `(BAP14)` becomes

~~~text
rank(P_(E,chi,n))/r_n ->2^(-m).                         (BAP15)
~~~

The corner contains the diffuse factor `L(W)`, so `r_n->infinity` along
the ultrafilter.  For every fixed `m` and `chi`, `(BAP15)` forces the
atom rank to tend to infinity.  This remains true in every nonzero full
multiplicity corner, independently of its trace.

If all `2^m` atom ranks were bounded by `K`, their sum would give

~~~text
r_n<=K 2^m,
m>=log_2(r_n)-log_2(K).                                 (BAP16)
~~~

Hence rank-one or uniformly bounded fibers require a window whose size grows
at least logarithmically with the matrix dimension.  Hyperlinear
quantifiers say that the error tends to zero for each fixed finite set; they
provide no estimate when the test window itself grows at the rate in
`(BAP16)`.  The corner theorem blocks dilution but cannot change this order
of quantifiers.

For a fixed actor `g` and window `E`, lift the two endpoint PVMs and the
actor unitary.  Covariance makes the `epsilon_j` in Step 1 tend to zero, and
`(BAP15)` makes the rank imbalance vanish.  Steps 1--3 therefore replace
the actor by a nearby unitary which permutes the coarse Boolean blocks.
Inside those blocks it remains an arbitrary unitary.

## Step 5: the fiber unitary can be maximally nonmonomial

Let `D=Nr` and let the atom projections on
`C^N tensor C^r` be

~~~text
E_i=|i><i| tensor I_r.
~~~

For a permutation `pi` of `[N]` and the normalized Fourier matrix `F_r`,
put

~~~text
U=P_pi tensor F_r.                                      (BAP17)
~~~

Then `UE_iU^*=E_(pi(i))` exactly.  Every row and column of `U` has its
nonzero entries in the prescribed target block, all with modulus
`1/sqrt(r)`.

An entrywise monomial unitary `M` selects one matrix entry in each row and
column.  Therefore

~~~text
|tr_D(M^*U)|<=1/sqrt(r).                                (BAP18)
~~~

Using `||U-M||_2^2=2-2 Re tr_D(M^*U)` gives

~~~text
||U-M||_2^2>=2-2/sqrt(r).                               (BAP19)
~~~

Thus exact coarse atom transport is compatible with asymptotically maximal
distance from every point permutation with phases.  Factoring any coarse
block normalizer by a chosen block-permutation representative leaves an
element of

~~~text
product_chi U(rank(P_chi)).                             (BAP20)
~~~

Actor multiplication constrains these elements only as a unitary cocycle.
Step 4 proves that every fixed-window factor in `(BAP20)` stays
unbounded in every positive-rank full corner.

The overlap coupling has therefore solved the pairwise coarse-normalizer
problem.  It has not produced a common rank-one masa or a jointly
multiplicative point action.  By `wreath-not-sofic`, such a global
extraction for the pinned model would contradict the known nonsoficity.
The remaining diffuse cocycle/moving-window theorem is exactly the open
hyperlinear-to-sofic step; no nonhyperlinearity conclusion is claimed.
