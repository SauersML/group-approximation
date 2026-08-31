---
rg: 2
id: prime-iwahori-complete-graph-hecke-proof
kind: route
title: Write the endpoint transfer in diagonal B-orbit coordinates
target: prime-iwahori-endpoint-transfer-is-complete-graph-hecke
requires:
  - regular-hecke-transfer-has-finite-fourier-sector-lmis
  - regular-hecke-second-moment-is-intersection-energy
---

For \(A\in D\), its matrix coefficients obey

\[
A_{bg,bh}=A_{g,h}\qquad(b\in B).
\]

The diagonal \(B\)-orbits in \(G\times G\) are parametrized by
\((Bh,u)\), with row \(hu^{-1}\) and column \(h\). This proves (PCG1) and
(PCG4), after multiplying by the constant which matches normalized
Hilbert--Schmidt counting.

Conjugation by \(\lambda(x)\), followed by the Reynolds average over
\(B\), gives

\[
(T_0A)_{hu^{-1},h}
 =\frac1{|B|}\sum_{b\in B}
 A_{xb^{-1}hu^{-1},\,xb^{-1}h}.
\]

The relative coordinate remains \(u\), while the column coset becomes
\(Bxb^{-1}h\). This is precisely (PCG2)--(PCG3). Right convolution
operators have coefficients depending only on \(u\), so the top
right-regular algebra is the constant-coset subspace. Fourier transform
in \(u\) gives (PCG5)--(PCG6).

For the prime Borel, the left cosets contained in \(BxB\) are indexed by

\[
B/(B\cap xBx)
\]

and number \(p\). None is \(B\), and they exhaust the other \(p\) points
of \(B\backslash G\). Every target coset occurs \(|B\cap xBx|\) times in
the average over \(b\), which proves (PCG7). The complete-graph spectrum
gives (PCG8)--(PCG9).

Finally, for \(Y=U^*\lambda(x)U\) and \(A\in D\),

\[
T_Y(AU)
 =E_D(\lambda(x)AUU^*\lambda(x)U)
 =E_D(\lambda(x)A\lambda(x))U
 =T_0(A)U.
\]

This proves (PCG10) and the transported top isometry.
