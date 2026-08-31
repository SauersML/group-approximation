---
rg: 2
id: hecke-rank-controls-coverage-but-has-half-space-ceiling
kind: claim
title: Hecke spectral rank controls coverage but has a half-space ceiling
distinct_from:
  near-top-hecke-coverage-has-exact-hole-dual: that computes optimal contractive coverage by an SDP; this extracts a dimension lower bound from its positive dual and then computes why that bound cannot close the regular Iwahori problem.
  hecke-top-spectrum-coverage-controls-window: that asks for a unital frame in a near-top band; this separates operator-module coverage from the raw dimension of that band.
  regular-core-window-is-a-hecke-kraus-hull: that gives the finite Hecke transfer; this computes its ordinary supertrace on the regular core.
---

Use the regular finite-core notation, with
(q=[G:B]),

[
D=(lambda_G(B))',qquad
T_X(A)=E_D(X_0AX),qquad
Q_epsilon=1_{[1-epsilon,1]}(T_X).
]

Let (c_epsilon) be the optimal contractive coverage from
`near-top-hecke-coverage-has-exact-hole-dual`, and put

[
r_epsilon=rac{operatorname{rank}(Q_epsilon)}
                  {dim_{mathbb C}D}.                 	ag{HRC1}
]

Then

[
c_epsilongeq r_epsilon,qquad
Delta^{m reg}_{G,B}(X)
 leqsqrt{2epsilon+4(1-r_epsilon)}.                 	ag{HRC2}
]

Thus near-full spectral rank would indeed produce the finite relative
corner.

For the regular core, however, near-full rank is impossible for a structural
reason.  If (x
otin B), then for every selfadjoint unitary (X),

[
operatorname{Tr}_{L^2(D)}(T_X)=0.                    	ag{HRC3}
]

Since (T_X) is a selfadjoint contraction, its eigenvalues lie in
([-1,1]).  If (k=operatorname{rank}(Q_epsilon)) and
(n=dim_{mathbb C}D), (HRC3) gives

[
0=sum_{i=1}^nlambda_i
 geq k(1-epsilon)-(n-k),
]

and hence

[
r_epsilonleqrac1{2-epsilon}.                     	ag{HRC4}
]

In particular (r_{epsilon_n}) cannot tend to one as
(epsilon_n	o0); it is asymptotically at most one half.  This applies
to every nondegenerate regular Iwahori quotient before using any of the
four residual estimates.

The trace calculation is exact.  Writing
(widehat B) for the irreducible representations of (B),

[
lambda_G|_Bcong
 igoplus_{piinwidehat B}piotimes1_{q d_pi},
qquad
Dcongigoplus_{piinwidehat B}M_{q d_pi}.         	ag{HRC5}
]

For (Z=(Z_pi)_piin D),

[
	au(Z)=rac1{|G|}sum_pi d_pioperatorname{Tr}(Z_pi),
qquad
dim_{mathbb C}D=q|G|,                               	ag{HRC6}
]

so right multiplication satisfies

[
operatorname{Tr}_{L^2(D)}(R_Z)
 =sum_pi qd_pioperatorname{Tr}(Z_pi)
 =(dim_{mathbb C}D)	au(Z).                         	ag{HRC7}
]

If (Zgeq0) is feasible in the coverage dual,
(Q_epsilon R_ZQ_epsilonsucceq Q_epsilon), then

[
operatorname{rank}(Q_epsilon)
 leqoperatorname{Tr}(Q_epsilon R_ZQ_epsilon)
 leqoperatorname{Tr}(R_Z)
 =(dim_{mathbb C}D)	au(Z).
]

Minimizing proves (HRC2).

For (HRC3), let (P_D) be the Reynolds projection onto (D):

[
P_D=rac1{|B|}sum_{bin B}
 L_{lambda(b)}R_{lambda(b)^*}.
]

The trace of (T_X) on (D) is the supertrace of
(P_D L_{X_0}R_XP_D) on (B(ell^2G)).  Cyclicity and (P_D^2=P_D)
reduce this to a sum of supertraces of left-right multipliers.  Every term
contains

[
operatorname{Tr}(lambda(xb))=0qquad(bin B),
]

because (x
otin B).  Hence the sum is zero.

At an exact endpoint a much smaller top space already contains the unit
and has coverage one.  Thus spectral rank is only a sufficient surrogate,
not the arithmetic invariant.  The moving problem remains the
(D)-module position of the near-top vectors, equivalently the positive
hole dual, and the nonhyperlinear-group root remains open.

DERIVATION
hecke-rank-half-space-ceiling-proof
