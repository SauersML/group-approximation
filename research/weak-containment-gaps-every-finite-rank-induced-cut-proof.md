---
rg: 2
id: weak-containment-gaps-every-finite-rank-induced-cut-proof
kind: route
title: Pass amenable induction through Fell absorption and test the adjoint gap on a projection
target: infinite-relative-induction-has-a-finite-rank-leakage-floor
requires: []
---

Let \(S\) and \(\kappa_S\) be as in (IFL1).

## 1. The induced representation is regular-tempered

Amenability of \(B\) gives equality of its full and reduced group
\(C^*\)-algebras. Therefore every unitary representation of \(B\), in
particular \(\beta\), is weakly contained in \(\lambda_B\):

\[
 \beta\prec\lambda_B.                                    \tag{WIC1}
\]

Unitary induction preserves weak containment, while induction in stages for
the regular representation gives

\[
 \pi=\operatorname{Ind}_B^\Gamma\beta
 \prec\operatorname{Ind}_B^\Gamma\lambda_B
 \cong\lambda_\Gamma.                                    \tag{WIC2}
\]

No finite-dimensionality hypothesis on \(\beta\) is needed for this step.

## 2. The Hilbert--Schmidt conjugation representation has the regular gap

Let \(\operatorname{Ad}\pi\) act on the Hilbert space
\(\mathcal S_2(H_\pi)\) of Hilbert--Schmidt operators by

\[
 (\operatorname{Ad}\pi)(g)T=\pi(g)T\pi(g)^*.
\]

Under the standard identification
\(\mathcal S_2(H_\pi)\cong H_\pi\otimes\overline{H_\pi}\),

\[
 \operatorname{Ad}\pi\cong\pi\otimes\overline\pi.
\]

Tensoring (WIC2) by \(\overline\pi\) and applying Fell absorption gives

\[
 \operatorname{Ad}\pi
 \prec\lambda_\Gamma\otimes\overline\pi
 \cong\lambda_\Gamma\otimes1_{\overline{H_\pi}}.          \tag{WIC3}
\]

The positive averaged Laplacian

\[
 \Delta_S={1\over |S|}\sum_{s\in S}(1-s)^*(1-s)
\]

is bounded below by \(\kappa_S\) in \(\lambda_\Gamma\). Weak containment and
positivity pass the same lower bound to (WIC3). Hence every
\(T\in\mathcal S_2(H_\pi)\) satisfies

\[
 {1\over |S|}\sum_{s\in S}
 \|\pi(s)T\pi(s)^*-T\|_{\mathrm F}^2
 \geq\kappa_S\|T\|_{\mathrm F}^2.                        \tag{WIC4}
\]

This is an ordinary nonamenability gap. Property \((T;FD)\) is neither used
nor applicable to the infinite representation \(\pi\).

## 3. A projection turns the adjoint gap into leakage

Let \(P\) have finite rank \(r>0\). It belongs to
\(\mathcal S_2(H_\pi)\) and \(\|P\|_{\mathrm F}^2=r\). For any unitary \(U\),

\[
 \|UPU^*-P\|_{\mathrm F}^2
 =2\bigl(r-\|PUP\|_{\mathrm F}^2\bigr)
 =2\|(1-P)UP\|_{\mathrm F}^2.                            \tag{WIC5}
\]

Apply (WIC4) to \(T=P\), use (WIC5) with \(U=\pi(s)\), and divide by \(r\).
This gives exactly (IFL2).

If \(P\) were invariant, every term in (WIC5) would vanish, contradicting
(IFL2). Thus the induced representation has no nonzero finite-dimensional
invariant summand.

## 4. Nearly unitary compression would have small leakage

For
\(C_s=P\pi(s)P|_{PH_\pi}\), unitarity of \(\pi(s)\) gives the exact defect
identity

\[
 \|(1-P)\pi(s)P\|_{\mathrm F}^2
 =r-\|C_s\|_{\mathrm F}^2.                               \tag{WIC6}
\]

If \(U_s\) is unitary on \(PH_\pi\) and
\(\|C_s-U_s\|_{\mathrm F}\leq\eta_s\sqrt r\), then

\[
 \|C_s\|_{\mathrm F}\geq(1-\eta_s)\sqrt r.
\]

For \(0\leq\eta_s\leq1\), (WIC6) yields

\[
 {1\over r}\|(1-P)\pi(s)P\|_{\mathrm F}^2
 \leq1-(1-\eta_s)^2
 \leq2\eta_s,                                           \tag{WIC7}
\]

which proves (IFL3). If every \(\eta_s<\kappa_S/4\), averaging (WIC7) would
make the left side of (IFL2) strictly smaller than \(\kappa_S/2\).
This proves (IFL4).

## 5. Iwahori specialization and scope

The relation \(rtr^{-1}=t^4\) identifies the core with the metabelian group
\(\mathbb Z[1/4]\rtimes\mathbb Z\), so it is amenable.
The modular subgroup of \(PSL_2(\mathbb Z[1/2])\) is nonamenable, hence the
ambient group is nonamenable. Steps 1--4 apply verbatim.

The finite quotient host
\(\operatorname{Ind}_{B_N}^{A_N}\beta\) is not a finite-rank almost-invariant
cut of \(\operatorname{Ind}_B^A\beta\). It is a different representation
created by annihilating the normal closure of \(t^N\). Therefore the proof
does not obstruct direct finite quotient descent. Instead it proves that
such descent, equivalently control of all translated normal rows or a full
relative positive-definite table, is indispensable before the finite-host
property-\((T;FD)\) argument can begin.

For sharpness, if \(\Gamma\) is amenable, take a Følner sequence
\(F_n\subset\Gamma\) and let \(P_n\) project
\(\ell^2(\Gamma)\) onto \(\ell^2(F_n)\). Then

\[
 \|(1-P_n)\lambda(s)P_n\|_{\mathrm F}^2
 =|\{g\in F_n:sg\notin F_n\}|,
\]

and the rank-normalized average tends to zero. This verifies the final
claim without asserting a converse for every induced representation.
