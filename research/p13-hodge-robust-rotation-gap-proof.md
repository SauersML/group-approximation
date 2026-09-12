---
rg: 2
id: p13-hodge-robust-rotation-gap-proof
kind: route
title: Sum the checked P13 replays against the exact Hodge coefficients
target: p13-hodge-robust-rotation-gap
requires:
  - p13-rotation-relator-defect-219
artifacts:
  - GroupApproximation/Sofic/LiteralP13HodgeData.lean
  - GroupApproximation/Sofic/LiteralP13HodgeReplay.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificateCore.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
---

Write

\[
w=(59,122,116,68,59,60,43,18,16,37,37,39,219)
\]

for the thirteen P13-relator costs from the checked rotation substitution.
All the calculations below are integer calculations on the tables already
present in the listed Lean files.

## 1. Support-product replay error

For a support pair \(p=(\ell,r)\), let \(m_{p,j}\) be the number of atoms with
`relatorIndex := j` in all chunks of the reduction used by
`supportProductL_R`; set \(m_{p,j}=0\) when that theorem closes by `rfl`.
Its rotation-weighted replay cost is

\[
M_p=\sum_{j=0}^{12}m_{p,j}w_j.
\]

There are 359 `rfl` pairs and 125 nontrivial pairs. The 144 reduction
certificates contain 4124 atoms in total; the largest unweighted reduction
area is 264 and the largest weighted area is 18888.

Let \(b_{ji\ell}\) be `boundaryNumerator j i ell`,
\(d_{i\ell}\) be `adjointCoboundaryNumerator i ell`, and
\(q_{ai\ell}\) be `qNumerator a i ell`. Put

\[
N_{ik\ell r}=
10^{16}\left(
  \sum_{j=0}^{12}b_{ji\ell}b_{jkr}
  +d_{i\ell}d_{kr}\right)
-\sum_{a=0}^{101}q_{ai\ell}q_{akr}.
\]

The entrywise replay majorant is

\[
F_{ik}=\sum_{\ell,r}|N_{ik\ell r}|M_{(\ell,r)}.
\]

Direct evaluation of the checked integer tables gives

\[
F=\begin{pmatrix}
8126150455782858985&10481676709221163080&5714522663355046414&11778459746068321824&11315998121936454142&12734867771111995253\\
11432644169224109010&11765734656646269058&10558022221274874295&12739165884383900412&8380916594753946643&10947122251247011992\\
6907508414434473441&8054504011078703383&6211817028006951466&7681219270621235824&8654490842003649799&6456593880959104825\\
11247638424246383266&12567404238164278847&8250977602679285025&7887096612624927507&12878726173064786600&8749311773016460342\\
9358257482783052639&8639836205761375607&10689686907896263896&8598677320356871566&13703045483149462958&8582798863889795935\\
12560377067202870386&14952227295209734641&9160319745005231768&8426281036411380798&10915991967276584155&10897125759158331155
\end{pmatrix}.
\]

Its exact row sums are

\[
\begin{split}
&(60151675467475839698,\ 65823605777530111410,\\
&\quad43966133447104118738,\ 61581154823796121587,\\
&\quad59572302263836822601,\ 66912322870264132903),
\end{split}
\]

and its exact column sums are

\[
\begin{split}
&(59632576013673747727,\ 66461383116081524616,\\
&\quad50585346168217652864,\ 57110899870466637931,\\
&\quad65849169182184884297,\ 58367820299382699502).
\end{split}
\]

Both maxima are strictly smaller than \(6692\cdot10^{16}\).
The block-operator Schur estimate therefore bounds the difference between the
free-word Hodge matrix and the evaluated collected certificate by
\(6692\delta\).

The exact residual row and column bound in
`LiteralP13HodgeCertificate.lean` is

\[
r=\frac{11670886519714}{10^{16}}.
\]

The scalar term is \(c=1/250\), while the Gram term remains positive for an
arbitrary unitary tuple. Hence the support-collected Hodge matrix \(H_U\)
satisfies

\[
\langle z,H_Uz\rangle\ge
(\gamma-6692\delta)\|z\|^2,\qquad
\gamma=c-r=\frac{28329113480286}{10^{16}}.
\tag{3}
\]

## 2. The Fox-prefix correction

The stored boundary coefficients are support-canonicalized. To compare them
with the raw Fox boundary, replay each nontrivial prefix through the checked
`prefixReplayN` theorem and weight its atoms by \(w\). The resulting
entrywise costs \(e_{ji}\), with rows indexed by the thirteen relators and
columns by the six generators, are

\[
e=\begin{pmatrix}
0&59&0&59&0&0\\
122&0&0&0&0&122\\
0&116&191&116&0&0\\
0&0&68&0&68&0\\
59&0&0&0&199&59\\
0&0&60&0&60&165\\
43&43&0&0&0&0\\
18&0&0&0&0&18\\
0&16&0&16&0&0\\
0&0&37&37&0&0\\
0&0&37&0&37&0\\
0&0&0&0&39&39\\
219&0&219&0&0&0
\end{pmatrix},
\qquad
\sum_{j,i}e_{ji}^2=299657.
\]

Thus, as an operator between Hilbert direct sums,

\[
\|B_{\rm can}(U)-B_{\rm raw}(U)\|
\leq\sqrt{299657}\,\delta.
\tag{4}
\]

The raw Fox identity is an identity in the free group, so for
\(z_i=(U_i-I)\xi\),

\[
(B_{\rm raw}(U)z)_j=(r_j(U)-I)\xi.
\]

Using the individual costs \(w_j\),

\[
\|B_{\rm raw}(U)z\|^2
\leq\left(\sum_jw_j^2\right)\delta^2\|\xi\|^2
=98175\delta^2\|\xi\|^2.
\tag{5}
\]

Equations (4), (5), and \((a+b)^2\leq2a^2+2b^2\) give

\[
\|B_{\rm can}(U)z\|^2
\leq196350\delta^2\|\xi\|^2
 +599314\delta^2\|z\|^2.
\tag{6}
\]

## 3. Quadratic gap and spectral exclusion

For \(z_i=(U_i-I)\xi\),

\[
\|z\|^2=\langle\xi,\Delta_U\xi\rangle
\]

and the \(DD^*\) part of the Hodge energy is
\(\|\Delta_U\xi\|^2\). Apply (3) to this \(z\), split the Hodge energy as
\(\|\Delta_U\xi\|^2+\|B_{\rm can}(U)z\|^2\), and insert (6). Rearrangement is
exactly

\[
(\gamma-6692\delta-599314\delta^2)
 \langle\xi,\Delta_U\xi\rangle
\leq\|\Delta_U\xi\|^2+196350\delta^2\|\xi\|^2.
\]

For an eigenvalue \(\lambda\) of \(\Delta_U\), this says

\[
\lambda^2-a_\delta\lambda+196350\delta^2\geq0,
\qquad
a_\delta=\gamma-6692\delta-599314\delta^2.
\]

The stated threshold is precisely the condition
\(a_\delta>2\sqrt{196350}\delta\). The forbidden open interval between the
two roots proves the claimed spectral containment. In arbitrary Hilbert
dimension the same conclusion follows from continuous functional calculus
for the bounded positive self-adjoint operator \(\Delta_U\).
