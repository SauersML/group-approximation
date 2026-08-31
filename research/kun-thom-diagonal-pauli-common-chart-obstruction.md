---
rg: 2
id: kun-thom-diagonal-pauli-common-chart-obstruction
kind: route
title: Lift the diagonal-coset counterexample to two incompatible marked Pauli atlases
target: commuting-sofic-pauli-atlases-need-not-glue
requires:
  - commuting-sofic-actions-need-not-combine
  - sofic-action-gives-marked-pauli-central-product-microstates
  - lamp-charts-recover-set-action
  - shared-center-extraspecial-wreath-has-fd-invisible-spin-sector
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
  - research/artifacts/sofic-action-pauli-central-product-microstates-2026-08-30.md
---

# Two individually classical Pauli models with no common chart

## 1. The diagonal-coset witness

Use the pinned Kun--Thom pair `Gamma<G).  The group `G` is residually
finite and hence sofic, while the action `G action G/Gamma` is not sofic.
Put

~~~text
Y=(G times G)/Delta Gamma,
Delta Gamma={(gamma,gamma):gamma in Gamma}.                     (1)
~~~

Let the first and second copies of `G` act by left multiplication in the
corresponding coordinate.  The claim
`commuting-sofic-actions-need-not-combine` proves all of the following:

1. the two actions `alpha_1,alpha_2:G action Y` commute;
2. each is free, hence sofic;
3. the combined action `alpha:G times G action Y` is transitive and
   nonsofic.

The last assertion follows because the diagonal orbit recovers the bad
coset action.  This is the established negative answer to GKP Question 4.2.

## 2. Apply the marked Pauli construction separately

Write elements of the common-center Pauli group as

~~~text
P_Y=F_2^(Y) times F_2^(Y) times F_2
~~~

with multiplication

~~~text
(u,v,e)(u',v',e')
 =(u+u',v+v',e+e'+<v,u'>).                                (2)
~~~

For a site `y`, put

~~~text
A_y=(delta_y,0,0),       B_y=(0,delta_y,0),       J=(0,0,1).
                                                                    (3)
~~~

Then

~~~text
[A_y,B_y]=J,       [A_y,B_z]=1 for y!=z,                  (4)
~~~

and the same-site pairs are permuted by every permutation of `Y`.

For `i=1,2`, both inputs of
`sofic-action-gives-marked-pauli-central-product-microstates` hold:
the actor `G` is sofic and `alpha_i` is a sofic set action.  Therefore

~~~text
P_Y semidirect_(alpha_i) G                                (5)
~~~

is sofic.  Moreover its proof gives approximations with

~~~text
d_Hamm(J,1)=1                                             (6)
~~~

at every stage: the source center is replicated as the nontrivial local
center on every chart carrier.  Thus loss of the central mark is not the
reason the two restricted models fail to combine.

## 3. A common Pauli chart would recover the forbidden action

Let `beta:G times G action P_Y` be the automorphism action induced by
`alpha).  Suppose that `beta` were a sofic-`C` action in the sense of
Alekseev--Bradford Definition 4.23, for some target class `C).

Choose a finite site window `E subset Y) and put the single-site generators
`A_y`, `y in E`, in the lamp window of the chart.  The chart maps are
injective on that finite lamp window and obey exact covariance on their good
carriers.  Since

~~~text
(g_1,g_2) A_y (g_1,g_2)^(-1)=A_(alpha(g_1,g_2)y),         (7)
~~~

reading the finitely many labels of the `A_y)'s gives exactly an orbit
approximation of the set action `alpha).  This is
`lamp-charts-recover-set-action`; neither the second Pauli coordinate nor
the value of the center is used in that transfer.

It follows that `alpha` would be a sofic action, contradicting Section 1.
Therefore `beta` has no such chart for any `C).  In particular, the two
models from Section 2 cannot be obtained as restrictions of one common
Pauli chart.

Notice the strength and the limitation.  Both restricted actor actions are
free and their marked Pauli semidirect products are honest sofic groups.
What fails is only the synchronization of the chart carriers.  An arbitrary
unitary microstate is not a chart, so this contradiction does not apply to a
non-Cartan Hilbert--Schmidt model.

## 4. What naming both Pauli generators recovers locally

The exact finite-packet calculation identifies why the missing datum is a
carrier rather than a tensor leg.

Let `Z subset Y` have `m` elements and let `rho` be an exact
finite-dimensional representation of its Pauli subgroup on the
`rho(J)=-I` sector.  The Pauli relations give

~~~text
H=(C^2)^(tensor Z) tensor C^r,
rho(P_Z)''=M_(2^m) tensor I_r.                            (8)
~~~

Let `D subset Z`, let `b:D->Z` be injective, and suppose a unitary `U`
satisfies, for every `x in D`,

~~~text
U rho(A_x) U^*=rho(A_(b x)),
U rho(B_x) U^*=rho(B_(b x)).                              (9)
~~~

Choose any permutation `b_bar of Z` extending `b`, and let
`P_(b_bar)` be its tensor-leg implementer.  Then

~~~text
C=P_(b_bar)^* U                                           (10)
~~~

commutes with both Pauli matrices on every leg in `D`.  Hence

~~~text
C in I_(2^|D|) tensor
     U(2^(m-|D|) r),                                     (11)
~~~

after ordering the `D)-legs first.  Equivalently,

~~~text
U=P_(b_bar) C.                                            (12)
~~~

For `D=Z`, (11) is the familiar arbitrary multiplicity factor
`I_(2^m) tensor U(r)).  For a proper partial window, the entire boundary
tensor factor joins that multiplicity.  Different extensions `b_bar`
differ by a unitary in exactly the same commutant.

Thus the named `A/B` pair intrinsically identifies every transported leg
which occurs in the window, but it cannot choose coherent completions on
the complement.  Actor multiplication turns the factors `C` into a
twisted boundary/multiplicity cocycle; it does not make the chosen
extensions multiply.  A probability space of coherent extensions on which
the actor maps are almost multiplicative is precisely the common finite
carrier that Section 3 proves cannot be supplied formally.

## 5. The exact GKP boundary for the original Kun--Thom action

For `X=G/Gamma`, put

~~~text
Pi_X=P_X semidirect G,
W_X=<A_x (x in X),G>.                                    (13)
~~~

The normal form in (2) shows

~~~text
W_X isomorphic to (direct_sum_X C_2) semidirect G,        (14)
~~~

the original Kun--Thom generalized wreath product.  Hence

~~~text
Pi_X hyperlinear  implies  W_X hyperlinear                (15)
~~~

because hyperlinearity passes to subgroups.  This implication does not make
the set action sofic.

GKP Theorem 3.8 is only the forward implication

~~~text
set action sofic + actor hyperlinear + base CE
 implies generalized wreath crossed product CE.          (16)
~~~

It contains no converse.  Their Question 4.4 asks for the converse in the
**sofic-group** metric, not the Hilbert--Schmidt metric.  At the sofic level,
a positive answer to Question 4.4 for the `C_2)-lamp, combined with
(14), would turn soficity of `Pi_X` into soficity of the set action.
At the hyperlinear level no such theorem is known; proving it for (14)
would already decide the original Kun--Thom hyperlinearity problem.

On the negative central corner, the second named Pauli coordinate replaces
the abelian Bernoulli base by

~~~text
e_- L(Pi_X)=R semidirect_crossed_product G,               (17)
~~~

where `R` is the infinite tensor product of the site `M_2)'s.
Equations (8)--(12) show that this strengthens fixed-window leg recognition
but leaves the common-chart seam unchanged.  Therefore

~~~text
Pi_X hyperlinear implies the action on X is sofic         (18)
~~~

would be a new quantum-to-classical wreath converse.  It is neither a
consequence of Theorem 3.8 nor a formal consequence of naming both Pauli
coordinates.  Establishing (18) would prove `Pi_X` nonhyperlinear; building
a hyperlinear `Pi_X` would in particular build the still-open hyperlinear
Kun--Thom subgroup `W_X`.  Neither conclusion is asserted here.

## Source boundary

The statements of GKP Definition 2.1(5), Theorem 3.8, and Questions 4.2 and
4.4 are transcribed verbatim in
`research/artifacts/gkp-2401-04945-verified.md`.  In particular,
Question 4.2 is a commuting-action question, Question 4.4 is a sofic
generalized-wreath converse, and neither is a published hyperlinear
converse.  Keeping those three statements separate is load-bearing.
