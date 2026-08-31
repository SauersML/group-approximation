---
rg: 2
id: boolean-atom-overlap-spatializes-arrows-corners-stay-diffuse
kind: claim
title: Boolean overlap spatializes each actor arrow, but every full corner keeps diffuse fibers
distinct_from:
  moving-lamp-refinement-cocycle-has-diffuse-fibers: that telescopes covariance to each refined atom and exhibits a supplied-normalizer fiber cocycle; this uses the joint overlap coupling of two whole atom PVMs to obtain a sum-of-squares block-spatialization bound.
  finite-lamp-targets-glue-after-action-groupoid-completion: that glues integer transports after a finite action groupoid has been supplied; this produces one coarse block transport for each actor arrow but shows why the positive-rank blocks do not supply a common point carrier.
  phase-free-cartan-observables-force-joint-lamp-targets: that assumes a common rank-one masa and then extracts point permutations; this proves that canonical hyperlinear models yield only coarse Boolean atoms and that no positive-density full corner can make those atoms rank one.
  elementary-abelian-regular-normalizers-have-diffuse-fibers: that gives an exact Fourier-fiber normalizer far from monomial on one invariant regular window; this proves the overlap estimate forcing coarse block transport in arbitrary models and shows the same fiber size diverges in every full corner.
  coset-wreath-wall-survives-full-commutant-corners: that preserves the canonical balanced wall and trace under full corners; this applies that trace identity to every finite Boolean atom and derives an unavoidable diffuse-multiplicity scale.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**ESTABLISHED PAIRWISE BLOCK SPATIALIZATION AND DIFFUSE-CORNER
OBSTRUCTION; GLOBAL ROUTE OPEN.**  Let
`v_1,...,v_m` and `w_1,...,w_m` be two commuting families of
self-adjoint unitaries in `M_d`.  Write their Boolean atom PVMs as

~~~text
P_chi=product_j (1+chi_j v_j)/2,
Q_psi=product_j (1+psi_j w_j)/2,     chi,psi in {+1,-1}^m. (BAO1)
~~~

For `U in U(d)` put `R_chi=U P_chi U^*` and

~~~text
mu(chi,psi)=tr(R_chi Q_psi),
epsilon_j=||U v_j U^*-w_j||_2.                           (BAO2)
~~~

Then `mu` is a nonnegative coupling of the two atom-rank distributions and

~~~text
eta:=sum_(chi!=psi) mu(chi,psi)
 <=(1/4)sum_j epsilon_j^2,                               (BAO3)

sum_chi ||R_chi-Q_chi||_2^2
 =2eta
 <=(1/2)sum_j epsilon_j^2.                               (BAO4)
~~~

If `rank(P_chi)=rank(Q_chi)` for every `chi`, there is
`C in U(d)` such that, for `V=CU`,

~~~text
V P_chi V^*=Q_chi                for every chi,
||V-U||_2^2=||C-I||_2^2
 <=2eta
 <=(1/2)sum_j epsilon_j^2.                               (BAO5)
~~~

Thus one finite actor covariance arrow always spatializes, with a
dimension-free root-sum-square bound, at the level of whole Boolean atoms.
If the ranks are only asymptotically equal, changing a total atom mass

~~~text
delta=(1/2)sum_chi |tr(P_chi)-tr(Q_chi)|                 (BAO6)
~~~

balances them; the additional direct-sum PVM error has squared norm
`2delta`.  Canonical fixed-window lamp moments make `delta->0`.

Now take the pinned Kun--Thom wreath
`W=(direct_sum_(G/Gamma) C_2) semidirect G` at `q=2` and assume,
conditionally, a trace-preserving embedding `Theta:L(W)->M` into a tracial
matrix ultraproduct.  Let `0!=e in Theta(L(W))' cap M` be a projection.
For a fixed lamp window `E` of size `m`, every atom `P_(E,chi)` satisfies

~~~text
tau_e(e Theta(P_(E,chi)))=2^(-m).                        (BAO7)
~~~

With projection lifts into a corner of dimension `r_n`, this says

~~~text
rank(P_(E,chi,n))/r_n -> 2^(-m).                         (BAO8)
~~~

Since `r_n->infinity`, every fixed-window atom rank tends to infinity in
every nonzero full corner.  In particular no positive-density full corner
turns the canonical finite lamp PVM into a rank-one PVM.  To make all atom
ranks bounded by `K` would require moving windows with

~~~text
|E_n| >= log_2(r_n)-log_2(K),                            (BAO9)
~~~

whereas hyperlinear convergence supplies moments only after each window is
fixed; it gives no rate at the scale `|E_n| comparable_to log r_n`.

The remaining fiber is metrically real.  On `C^N tensor C^r`, let
`P_pi` permute the `N` Boolean atoms and let `F_r` be the Fourier unitary.
Then

~~~text
U=P_pi tensor F_r                                       (BAO10)
~~~

has exact atom transport, but for every entrywise monomial unitary `M`,

~~~text
||U-M||_2^2 >=2-2/sqrt(r).                               (BAO11)
~~~

Thus the pairwise overlap theorem reaches block monomiality and no farther.
The residual groups `product_chi U(rank(P_chi))` remain diffuse in every
positive-rank full corner, and actor multiplication lives as a cocycle in
those groups.  Extracting one common rank-one refinement, or proving that
this cocycle is point-spatial on a moving window of logarithmic size, is
exactly the missing hyperlinear-to-sofic theorem.  Nothing here proves that
`W` is nonhyperlinear.

DERIVATION
boolean-atom-overlap-coupling-and-diffuse-corner-proof
