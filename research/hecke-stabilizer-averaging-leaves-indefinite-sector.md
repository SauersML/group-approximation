---
rg: 2
id: hecke-stabilizer-averaging-leaves-indefinite-sector
kind: claim
title: Exact Hecke stabilizer averaging leaves an indefinite sector
distinct_from:
  hecke-frame-failure-has-right-multiplier-dual: that gives an arbitrary Farkas separator for frame failure; this identifies the exact stabilizers under which it may be averaged and proves that a full-support indefinite separator can survive them.
  near-top-hecke-coverage-has-exact-hole-dual: that gives a positive majorant dual for optimal contractive coverage; this shows how such a dual may be centralized but why approximate residual symmetries do not preserve its sharp spectral band.
  regular-core-window-is-a-hecke-kraus-hull: that identifies the relative matrix range; this audits the symmetry reduction of the finite Hecke transfer problem.
---

Let (G=langle B,xangle) be finite, let
(D=(lambda_G(B))'), (X_0=lambda_G(x)), and let
(X=X^*=X^{-1}) be a supplied extender.  Put

[
T_X(A)=E_D(X_0AX),qquad
C_0=Dcap{X_0}',qquad C_X=Dcap{X}'.              	ag{HSA1}
]

Then

[
C_0=lambda_G(G)'=mathbb C[G]^{m op},              	ag{HSA2}
]

and the Hecke transfer is exactly bimodular in the following sense:

[
T_X(LAR)=L,T_X(A),R
quad(Lin C_0, Rin C_X, Ain D).                  	ag{HSA3}
]

Consequently every spectral subspace of (T_X), in particular

[
{cal H}_epsilon
 =1_{[1-epsilon,1]}(T_X)L^2(D),                      	ag{HSA4}
]

is a (C_0)--(C_X) bimodule.

This gives the strongest canonical exact separator averaging.  If
(Z=Z^*in D) satisfies

[
	au(Z)>0,qquad
P_epsilon R_ZP_epsilonpreceq0,                     	ag{HSA5}
]

then Haar averaging over (U(C_X)) produces another separator

[
overline Z=int_{U(C_X)}U ZU^*,dU
 in C_X'cap D,qquad 	au(overline Z)=	au(Z).       	ag{HSA6}
]

The same averaging preserves positivity and the reverse inequality
(P_epsilon R_ZP_epsilonsucceq P_epsilon) in the optimal-coverage
dual.  The left stabilizer (C_0=mathbb C[G]^{m op}) does not further
average (Z): left multiplication by (C_0) commutes with every right
multiplier (R_Z).

Crucially, (HSA6) does not eliminate the indefinite branch, even with full
right support and exact two-sided bimodule symmetry.  For arbitrary
(a,cgeq1), take

[
D=M_aotimes M_2otimes M_c,quad
C_0=M_aotimes1otimes1,quad C=1otimes1otimes M_c,
]

and

[
v=egin{pmatrix}1&0\0&2end{pmatrix},qquad
{cal H}=M_aotimesmathbb Cvotimes M_c.              	ag{HSA7}
]

The subspace ({cal H}) is a (C_0)--(C) bimodule and contains the
invertible element (1otimes votimes1), so it has full right support.
Nevertheless

[
Z=1otimes
 egin{pmatrix}2&0\0&-1end{pmatrix}
 otimes1in C'cap D                                  	ag{HSA8}
]

has (	au(Z)=1/2), while for every (Ain{cal H}),

[
	au(ZA^*A)
 =-|A|_2^2<0quad(A
e0).                            	ag{HSA9}
]

Thus (Z) is already stabilizer-averaged, indefinite, and separates the
unit from the Hecke-frame cone although that subspace has full support.
Taking (T) to be the orthogonal projection onto ({cal H}) realizes
({cal H}) as the sharp top band of a selfadjoint bimodular contraction.
Hence bimodularity and stabilizer averaging alone cannot prove coverage.

Nor can vanishing approximate covariance be substituted for exact band
invariance.  On (mathbb C^2), let

[
S_eta=operatorname{diag}(1,1-eta),qquad
W=egin{pmatrix}0&1\1&0end{pmatrix}.
]

Then (|WS_eta-S_eta W|=eta), but

[
Q_eta=1_{[1-eta/2,1]}(S_eta)
 =operatorname{diag}(1,0),qquad
|WQ_eta-Q_eta W|=1.                               	ag{HSA10}
]

Therefore even an (o(1)) covariance estimate extracted from the four
Iwahori residuals does not justify averaging a certificate inside a moving
sharp near-top band without a spectral-margin estimate or a soft-filter
replacement.

For the regular congruence core,
(Dcong M_{[G:B]}(mathbb C[B]^{m op})), and (HSA2)--(HSA6) are exact
at every level.  They reduce a candidate certificate to the relative
commutant of the supplied extender's exact stabilizer, but (HSA7)--(HSA10)
show that this formal reduction cannot yield a uniform anti-separator
estimate.  One must use additional arithmetic of the concrete Iwahori
Hecke matrix to rule out the surviving sector, or construct it in an
actual congruence sequence.  Neither is currently known, so the
nonhyperlinear-group root remains open.

DERIVATION
hecke-stabilizer-indefinite-sector-proof
