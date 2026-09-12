---
rg: 2
id: regular-hecke-fourier-sector-lmi-proof
kind: route
title: Fourier-decompose the right-regular symmetry of the Hecke module
target: regular-hecke-transfer-has-finite-fourier-sector-lmis
requires:
  - hecke-stabilizer-averaging-leaves-indefinite-sector
  - near-top-hecke-coverage-has-exact-hole-dual
  - regular-hecke-second-moment-is-intersection-energy
---

The algebra \(\varrho(G)\) lies in \(D\) and commutes with
\(X_0=\lambda_G(x)\). Bimodularity of \(E_D\) gives

\[
T_X(\varrho(g)A)=\varrho(g)T_X(A),
\]

so the transfer commutes with the representation (HFS1).

Its character is regular with multiplicity \(q\). Indeed, extend left
multiplication by \(\varrho(g)\) to the full Hilbert--Schmidt space and
insert the Reynolds projection

\[
P_D=\frac1{|B|}\sum_{b\in B}
 L_{\lambda(b)}R_{\lambda(b)^*}.
\]

Then

\[
\operatorname{Tr}_{L^2(D)}({\mathsf L}_g)
 =\frac1{|B|}\sum_{b\in B}
 \operatorname{Tr}\!\left(\lambda(b)\varrho(g)\right)
 \operatorname{Tr}\!\left(\lambda(b)^*\right).
\]

Only \(b=1\) survives. The remaining term is zero for \(g\ne1\), while
for \(g=1\) it is \(|G|^2/|B|=q|G|=\dim_{\mathbb C}D\). This proves
(HFS2). Schur decomposition of the commuting selfadjoint operator \(T_X\)
gives (HFS3)--(HFS4).

Associativity gives
\({\mathsf L}_gR_Z=R_Z{\mathsf L}_g\) for every \(Z\in D\).
The restriction of the right regular action of \(D\) to each whole-group
multiplicity space is the star-representation \(\sigma_\pi\) of the
opposite algebra, proving (HFS5). Substituting (HFS4)--(HFS5) into the
positive compressed-multiplier dual gives (HFS6), and tracing (HFS3)
gives (HFS7).

Finally, at \(X=X_0\), the top vectors are precisely the operators
commuting with both \(\lambda(B)\) and \(\lambda(x)\). Since these generate
\(\lambda(G)\), the top space is \(\lambda(G)'\). Its left multiplication
character is one regular character, so its \(\pi\)-multiplicity is
\(d_\pi\), proving (HFS8).
