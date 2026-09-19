---
rg: 2
id: post-gap-compressor-constants
kind: claim
title: The post-gap compressor vector chain has exact constants 8, 64, 64
distinct_from:
  effective-transport-modulus: That root asks for a displayed-relator modulus from the literal presentation; this claim closes only the finite-dimensional analytic chain once its three stage inputs are supplied.
  p13-hodge-robust-rotation-gap: That is the robust rotation spectral gap; this is the later corner, transport, and marked-commutator budget.
artifacts:
  - GroupApproximation/Sofic/MarkedCompressionVectorChain.lean
  - GroupApproximation/Sofic/MarkedCompressionSequentialKill.lean
  - GroupApproximation/Sofic/MarkedCompressionRootCapture.lean
  - GroupApproximation/Sofic/KazhdanCompressorCorner.lean
  - GroupApproximation/Sofic/KazhdanAsymptoticCommutant.lean
---

Let \(P\) be an orthogonal projection on the row-vectorized matrix Hilbert
space, let \(T,A\) be unitaries, and put \(Q=TPT^*\).  For a vector \(\xi\),
assume

\[
 \|(A-I)P\|\le f,\qquad
 \|(I-P)Q\|\le \ell,\qquad
 \|(I-P)\xi\|_2^2\le c.
\]

Then the transported displacement satisfies the dimension-free inequality

\[
 \|A(T\xi)-T\xi\|_2^2
 \le (2f^2+16\ell^2)\|\xi\|_2^2+16c.
\tag{PG1}
\]

When \(\xi\) is the row vectorization of a unitary \(C\), normalized by the
matrix dimension, this becomes

\[
 d_{\mathrm{HS}}^2\!\left(
   U_a(U_t C U_t^*)U_a^*,\,U_t C U_t^*
 \right)
 \le 2f^2+16\ell^2+16c.
\tag{PG2}
\]

Consequently the marked commutator of those two unitary matrices obeys

\[
 d_{\mathrm{HS}}^2([D,U_aDU_a^*],I)
 \le 8f^2+64\ell^2+64c,
 \qquad D=U_t C U_t^*.
\tag{PG3}
\]

These are the exact theorems
`MarkedCompressionVectorChain.transported_displacement_le`,
`conjugated_transport_hsDistSq_le`, and
`marked_commutator_hsDistSq_le`.

The budget used by
`MarkedCompressionSequentialKill.commutatorMatrix_hsDistSq_vanishing`
is therefore exact:

\[
 f^2=\varepsilon/24,\qquad
 \ell^2=\varepsilon/192,\qquad
 c=\varepsilon/192,
\]

because

\[
 8(\varepsilon/24)+64(\varepsilon/192)+64(\varepsilon/192)
 =\varepsilon.
\tag{PG4}
\]

There is no hidden dimension loss in (PG1)--(PG4).

## Finite-stage input ledger

The three inputs have the following quantitative meanings in the repository.

1. **Top-corner fixing.**  If a positive Laplacian
   \(\Delta=\sum_{s\in S}(2I-U_s-U_s^*)\) has spectrum in
   \([0,\lambda_-]\cup[\lambda_+,\infty)\), and \(P\) is its low spectral
   projection, then

   \[
   \sum_{s\in S}((U_s-I)P)^*((U_s-I)P)=P\Delta P,
   \]

   hence every \(s\in S\) satisfies
   \(\|(U_s-I)P\|\le\sqrt{\lambda_-}\).
   A fixed word of length \(L\) costs at most \(L\sqrt{\lambda_-}\), plus
   the explicitly replayed multiplication/inverse defects for that word.

2. **One-sided leakage and equal-rank flip.**  In
   `KazhdanCompressorCorner.one_sub_moved_mul_corner_vanishing`, an
   operator bound

   \[
   \|(I-H)T^*P\|\le (1-\theta)e_0^2
   \]

   implies \(\|(I-Q)P\|\le e_0\).  Equal rank then gives

   \[
   \|(I-P)Q\|\le
   \frac{e_0}{\sqrt{1-e_0^2}}.
   \]

   The committed implementation chooses
   \(e_0=\min(1/2,\ell/2)\), which makes the last quantity at most
   \(2e_0\le\ell\).

3. **Root capture.**  If the averaged root residual has operator norm at
   most \(\eta\), the spectral capture calculation gives

   \[
   \|(I-P)\operatorname{rowVec}(C)\|_2^2
   \le \frac{\eta}{1-\theta}\,d.
   \]

   Thus the code takes
   \(\eta=(1-\theta)\varepsilon/192\), yielding
   \(c=\varepsilon/192\).

For a uniformly bounded asymptotic-commutant sequence with operator bound
\(M\), `KazhdanAsymptoticCommutant.transport_of_leakage` uses

\[
 q=\min\!\left(1,\frac{\varepsilon}{40(M^2+1)}\right)
\]

and obtains the sharper intermediate stage formula

\[
 18q^2M^2+16q\le\varepsilon.
\tag{PG5}
\]

## What remains before an end-to-end displayed-relator modulus

The analytic vector-chain constants are closed.  Instantiating them from the
literal presentation still requires two genuinely separate finite
certificates:

- a robust **full affine-base** spectral split.  The P13 certificate currently
  supplies only the rotation split;
- replay tables for the finitely many fixed compressor, corner, root, and
  marked-word products used to make the three inputs above functions of the
  displayed-relator defect.

The first item is the first mathematical gate.  The second is finite
bookkeeping once the first exists.  In particular, (PG1)--(PG5) must not be
cited as an end-to-end modulus by themselves.
