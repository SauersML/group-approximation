---
rg: 2
id: hecke-stabilizer-indefinite-sector-proof
kind: route
title: Centralize the Hecke dual and exhibit its surviving middle sector
target: hecke-stabilizer-averaging-leaves-indefinite-sector
requires:
  - hecke-frame-failure-has-right-multiplier-dual
  - near-top-hecke-coverage-has-exact-hole-dual
  - regular-core-window-is-a-hecke-kraus-hull
---

Since (G=langle B,xangle),

[
Dcap{X_0}'={lambda_G(B),lambda_G(x)}'
 =lambda_G(G)'=mathbb C[G]^{m op}.
]

For (L) in this algebra and (Rin Dcap{X}'), commute (L) past
(X_0), commute (R) past (X), and use (D)-bimodularity of (E_D)
to obtain (T_X(LAR)=LT_X(A)R).  Functional calculus makes every spectral
projection of (T_X) commute with the corresponding left and right
multiplication operators.

If (Uin U(C_X)), right multiplication (mathsf R_U:Amapsto AU)
preserves the spectral band and

[
mathsf R_U^*R_Zmathsf R_U=R_{UZU^*}.
]

Conjugating either compressed multiplier inequality and integrating over
(U(C_X)) proves the averaging statement.  Left multiplication commutes
with (R_Z), so the canonical left stabilizer supplies no conjugation of
the multiplier.

For the finite model, reorder the outer tensor factors and write every
element of ({cal H}) as (Potimes v), with
(Pin M_aotimes M_c).  With normalized traces,

[
	au_2!left(
 egin{pmatrix}2&0\0&-1end{pmatrix}v^2
ight)=rac{2-4}{2}=-1.
]

This gives (	au(ZA^*A)=-	au(P^*P)=-|A|_2^2).
The invertibility of (1otimes votimes1) proves full right support,
while the displayed strict inequality proves that no sum of
(A_j^*A_j) can equal the unit.  The orthogonal projection onto this
two-sided module commutes with its left and right unitary actions, so it is
a selfadjoint bimodular contraction with precisely this top band.

Finally, direct multiplication gives
(|[W,S_eta]|=eta), whereas the indicated sharp spectral projection
is moved to its orthogonal complement by (W), giving commutator norm one.
This proves the sharp-band firewall.
