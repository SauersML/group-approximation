---
rg: 2
id: tv-two-row-hs-wall-and-refinement-no-go-proof
kind: route
title: Compute the two-row Hilbert--Schmidt wall and audit the decreasing-noise diagonal
target: tv-antipodal-pair-forbids-coherent-negative-sign-refinement
requires:
  - taller-vidick-positive-noise-collapses-central-sign
  - taller-vidick-positive-noise-fixed-support-reweighting
  - reverse-kleene-does-not-remove-tv-completeness-loss
---

# Compute the two-row Hilbert--Schmidt wall and audit the decreasing-noise diagonal

## 1. The old presentation contains an antipodal pair

Fix a positive-noise Taller--Vidick test. Choose any supported outer tuple
\((W,U,C)\), a query \(f\in F_U\), and \(g\in F_W\). Lift \(f\) from \(U\)
to \(W\). The two masks

\[
 \mu_+=f^\uparrow,\qquad \mu_-=-f^\uparrow             \tag{1}
\]

both have positive probability for every \(0<\epsilon<1\). Use query \(f\)
with \(\mu_+\) and query \(-f\) with \(\mu_-\). In both cases the third
query is

\[
 g'=fg\mu_+=g,\qquad g'=(-f)g\mu_-=g.                   \tag{2}
\]

Folding identifies the first variable in the two rows, while the folding
sign changes. The two LCS equations therefore have one literal left word
\(L\) and opposite right-hand sides:

\[
 L=J^a,\qquad L=J^{a+1}.                                \tag{3}
\]

No source-game property enters (1)--(3).

Let

\[
 r_+=LJ^{-a},\qquad r_-=LJ^{-(a+1)}.                    \tag{4}
\]

Since \(J\) is a central involution,

\[
 r_-=r_+J.                                               \tag{5}
\]

## 2. Exact corner identity

Evaluate the old free generators by arbitrary unitaries in a finite
tracial von Neumann algebra \((M,\tau)\). Assume only that the evaluated
\(J\) is an exact central involution. Put

\[
 p_-=\frac{1-J}{2},\qquad \eta=\tau(p_-).                \tag{6}
\]

On \(p_-M\), equation (5) becomes \(r_-=-r_+\). If

\[
 t=\operatorname{Re}\tau(p_-r_+),
\]

then unitary invariance and centrality give

\[
 \begin{aligned}
 \|p_-(r_+-1)\|_2^2&=2\eta-2t,\\
 \|p_-(r_--1)\|_2^2&=\|p_-(r_++1)\|_2^2=2\eta+2t.
 \end{aligned}                                          \tag{7}
\]

Adding proves the exact identity

\[
 \|p_-(r_+-1)\|_2^2+\|p_-(r_--1)\|_2^2=4\eta.           \tag{8}
\]

Thus at least one defect is at least \(\sqrt{2\eta}\). On a full
negative sector, \(\eta=1\), so the lower bound is \(\sqrt2\).

If the two rows have fixed weights \(q_+,q_->0\), then

\[
 \begin{aligned}
 q_+\|p_-(r_+-1)\|_2^2+
 q_-\|p_-(r_--1)\|_2^2
 &\geq \min(q_+,q_-)
       \left(\|p_-(r_+-1)\|_2^2+
             \|p_-(r_--1)\|_2^2\right)\\
 &=4\min(q_+,q_-)\eta.                                  \tag{9}
 \end{aligned}
\]

This is the sharp two-row version of the weighted van Kampen bound. It has
no proof-area loss.

## 3. Why a coherent word refinement cannot exist

Suppose that for \(n<m\) one assigns to every generator of the old free
presentation a word in the later generators. Evaluate those later words in
any strategy or approximate representation. If the assignment sends the
old \(J_n\) to the later central sign \(J_m\), the two images of (3) still
have the same image left word and opposite powers of \(J_m\). Equations
(8)--(9) apply without requiring the assignment to descend to a
homomorphism.

Consequently, if the later negative-\(J_m\) mass is bounded below, the
images of all old relators cannot have defect tending to zero. This rules
out both proposed versions of coherence:

\[
 \max_{r\in R_n}\|r(\text{later words})-1\|_2
   =O(\epsilon_m)                                       \tag{10}
\]

and, for the fixed old row weights,

\[
 \sum_{r\in R_n}q_{n,r}
   \|r(\text{later words})-1\|_2^2
   =O(\epsilon_m).                                      \tag{11}
\]

The right sides of (10)--(11) tend to zero, while (8)--(9) stay positive.

If the word assignment were required to descend to a group homomorphism,
the obstruction is even more elementary. The old solution group satisfies
\(J_n=1\), so every homomorphism sends \(J_n\) to the identity. It cannot be
a marked homomorphism into a group where the proposed target sign is
nontrivial.

## 4. The support discontinuity is the exact non-nesting equation

At positive noise, both masks in (1) occur. At zero noise, only the
constant-one mask occurs, so at least one member of the pair is absent in
general. The zero-noise equation set is therefore not a refinement of any
positive-noise equation set.

One might try to retain an approximate image of the deleted row rather
than a literal row. But retaining approximate images of both old rows is
precisely (10), and (8) forbids it on the honest negative sector. Thus the
failure is not merely that the outer repeated contexts at levels \(n\) and
\(n+1\) have different names. Even after granting arbitrary word maps
between those variables, the antipodal pair itself cannot nest.

This also explains the completeness estimate. The honest positive-noise
strategy has small expected loss because rare mask rows carry small
probability. It does not have small conditional loss on every row. For the
fixed pair (3), one of the two conditional relator defects is always
macroscopic by (8). Sending later noise to zero only changes its later
sampling weight; it does not make a fixed old row accurate.

## 5. Quantitative perfect-versus-imperfect completeness audit

Proposition 4.1 of Taller--Vidick states, for synchronous finite-dimensional
strategies, that

\[
 \omega_q^s(L^\epsilon(u,B,\pi))
 \geq 1-\frac1{36}(1-\delta)^2
 \quad\Longrightarrow\quad
 \omega_q(G(B,\pi)^{\otimes u})\geq4\epsilon\delta^2.
                                                               \tag{12}
\]

Hence, after choosing \(u\) so that the repeated source value is below
\(4\epsilon\delta^2\), the contrapositive gives

\[
 \omega_q^s(L^\epsilon(u,B,\pi))
 <1-\frac1{36}(1-\delta)^2.                             \tag{13}
\]

The limiting long-code threshold as \(\delta\) tends to zero is \(35/36\),
but \(\delta=0\) makes the conclusion on the right side of (12) tautological.
The concrete parameters in the proof of Theorem 5.2 are

\[
 \delta=1-\frac1{\sqrt2},\qquad
 0<\epsilon<\frac1{72},\qquad
 s'=\frac{71}{72}.                                      \tag{14}
\]

Thus the published RE-hardness theorem uses completeness \(1-\epsilon\)
and a strict constant soundness bound, concretely \(71/72\) in its
synchronous analysis. The paper separately sketches the conversion to
general quantum strategies with a weaker constant. Referring simply to
\(35/36\) suppresses the positive-\(\delta\) and repetition quantifiers.

Lemma 4.2 gives the honest bound

\[
 \omega_q^s(L^\epsilon(u,B,\pi))\geq1-\epsilon           \tag{15}
\]

when the source has the required perfect synchronous strategy. Its
operator formula uses only PVM relations and a trace, so the same
construction applies in a tracial commuting representation. Therefore a
perfect commuting source can yield a near-perfect commuting output. It
cannot yield a perfect output: (3) proves \(J=1\), and (8) gives a direct
positive loss for every negative-sign model.

At \(\epsilon=0\), the honest estimate becomes perfect and the antipodal
pair can disappear. But the decoder conclusion in (12) becomes

\[
 \omega_q(G(B,\pi)^{\otimes u})\geq0,                   \tag{16}
\]

which has no soundness content. The main theorem chooses \(u\) after
\(\epsilon\) so that a positive repeated-game bound is strictly below
\(4\epsilon\delta^2\); at zero noise this would require a nonnegative value
to be strictly below zero. Thus the published proof cannot transfer a
Lin-style perfect commuting source to a perfect LCS while retaining any
strict qa bound.

## 6. The diagonal and fixed point both stop at the same two rows

Let \(A_n\) be the area of a proof that \(J_n=1\). Choosing a later noise
with \(\epsilon_{n+1}\ll A_n^{-2}\) could help only if the later honest
strategy made every old relator small. Here the certificate (3) already has
area two, and (8) says its negative-corner defect sum is exactly four.
There is no diagonal inequality to cross.

Likewise, a fixed-point machine which enumerates proofs of \(J=1\) in its
own positive-noise output always finds (3) and halts. Near-completeness
causes no contradiction. If the machine waits only for a certificate whose
weighted gap exceeds \(\epsilon\), then nonhalting no longer implies
\(J\ne1\): the algebraic proof (3) exists regardless of whether it passes
the numerical filter.

The only way out is to change the finite equations so that the antipodal
pair is absent while a new dimension-independent zero-noise decoder
survives. A source-dependent shared cyclic or higher-occurrence system is
not covered by this theorem. Coherent refinement of the published
positive-noise supports is closed.

Primary source:

- Aviv Taller and Thomas Vidick, Approximating the quantum value of an LCS
  game is RE-hard, Proposition 4.1, Lemma 4.2, and Theorem 5.2,
  https://arxiv.org/abs/2507.22444
