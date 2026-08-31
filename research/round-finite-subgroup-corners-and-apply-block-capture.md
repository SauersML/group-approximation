---
rg: 2
id: round-finite-subgroup-corners-and-apply-block-capture
kind: route
title: Round almost-reducing torsion corners and invoke bounded-payload capture
target: approximate-central-tensor-coverage-forces-capture
requires:
  - bounded-payload-congruence-tensors-have-uniform-capture
---

# Torsion corners round with linear Hilbert--Schmidt cost

Write \(\|\cdot\|_{2,d}\) for the Hilbert--Schmidt norm normalized on the
whole \(d\)-dimensional space, and put \(q=1-p\) temporarily for the
orthogonal complementary projection. Let \(U\) be unitary, \(U^m=1\), and
set
\[
 T=pUp:p\mathbb C^d\longrightarrow p\mathbb C^d,\qquad
 \delta=\|[p,U]\|_{2,d}.                                  \tag{1}
\]
The leakage identity
\[
 p-T^*T=pU^*qUp=((qUp)^*(qUp))                            \tag{2}
\]
shows that a unitary completion \(V\) of the polar part of \(T\) satisfies
\[
 \|T-V\|_{2,d}^2
 \leq\operatorname{tr}_d(p-T^*T)
 =\|qUp\|_{2,d}^2\leq\delta^2.                            \tag{3}
\]
This also covers a nontrivial kernel: extend the partial polar isometry
arbitrarily between its equal-dimensional missing initial and final
subspaces. For contractions, telescoping after inserting \(p+q=1\) gives
\[
 \|T^m-p\|_{2,d}\leq(m-1)\delta,
 \qquad
 \|V^m-p\|_{2,d}\leq(2m-1)\delta.                         \tag{4}
\]
For completeness, the first estimate follows inductively from
\[
 T^{k+1}-pU^{k+1}p
 =T(T^k-pU^kp)-pUqU^kp,
\]
and the second follows by telescoping \(V^m-T^m\).

Round each spectral value of \(V\) to a nearest \(m\)-th root of unity.
If \(W\) is the resulting unitary, then \(W^m=p\) and, pointwise on the
unit circle,
\[
 |z-W(z)|\leq |z^m-1|.
\]
Consequently
\[
 \|T-W\|_{2,d}\leq 2m\delta.                              \tag{5}
\]
Apply (5) independently with \(m=2\) and \(m=3\) to the compressed
order-two and order-three generators in each modular vertex. Since
\(\operatorname{PSL}_2(\mathbb Z)=C_2*C_3\), the rounded matrices define
exact representations of both vertices on \(p\mathbb C^d\). Taking the
maximum over the four generators proves (ACT2), with a universal constant
in the whole-space normalization. Passing to the corner-normalized norm
costs a factor \(q^{-1/2}\), which is bounded by \(q_0^{-1/2}\).

# The edge defect survives compression and rounding

Return to the notation \(r=1-\operatorname{tr}_d(p)\) of the claim, and
write \(\widehat\pi^p\) for the rounded exact vertex pair on the corner.
Every edge generator is represented by a fixed word in the two torsion
generators. Repeatedly inserting \(p+(1-p)=1\), and then using (5), gives
for every such fixed word \(w\)
\[
 \|\widehat\pi^p_\epsilon(w)-p\pi_\epsilon(w)p\|_{2,d}
 \leq C_w\Omega(p,\pi).                                  \tag{6}
\]
Compressing the original edge discrepancy cannot increase its
whole-space Hilbert--Schmidt norm. Since the edge generating set and all
word lengths are fixed, (6) yields
\[
 \operatorname{def}(\widehat\pi^p)
 \leq C q^{-1/2}
 \bigl(\operatorname{def}(\pi)+\Omega(p,\pi)\bigr).       \tag{7}
\]

Suppose now that an exact corner pair \(\kappa\) in the bounded-payload
congruence tensor hull of payload size at most \(D\) satisfies
\[
 d_{2,p}(\widehat\pi^p,\kappa)\leq\zeta.                  \tag{8}
\]
Fixed-word Lipschitz continuity and (7) imply
\[
 \operatorname{def}(\kappa)
 \leq Cq^{-1/2}
 \bigl(\operatorname{def}(\pi)+\Omega(p,\pi)\bigr)
     +C\zeta.                                             \tag{9}
\]
By **bounded-payload-congruence-tensors-have-uniform-capture**, after
decreasing its exponent if necessary so that \(0<\alpha_D\leq1\), there
is a compatible endpoint \(\widetilde\kappa\) of the same corner dimension
with
\[
 d_{2,p}(\kappa,\widetilde\kappa)
 \leq C_D\operatorname{def}(\kappa)^{\alpha_D}.           \tag{10}
\]
Combining (8)--(10), using \(q\geq q_0\), and absorbing linear terms into
the power on the bounded defect interval gives
\[
 d_{2,p}(\widehat\pi^p,\widetilde\kappa)
 \leq C_{D,q_0}
 \bigl(\operatorname{def}(\pi)+\Omega(p,\pi)+\zeta
 \bigr)^{\alpha_D}.                                      \tag{11}
\]

# Reinsert the uncovered carrier

On \(p\mathbb C^d\), use the endpoint from (11). On
\((1-p)\mathbb C^d\), use the trivial compatible representation. For each
original generator, deleting its two off-diagonal blocks costs at most a
fixed multiple of \(\Omega(p,\pi)\). The remaining complementary diagonal
block differs from the identity by at most \(2\sqrt r\) in the
whole-space normalized Hilbert--Schmidt norm. The corner contribution in
(11) is multiplied by \(\sqrt{1-r}\leq1\). Thus the triangle inequality,
with the linear off-diagonal term absorbed as above, proves
\[
 D(\pi)\leq2\sqrt r+
 C_{D,q_0}
 \bigl(\operatorname{def}(\pi)+\Omega(p,\pi)+\zeta
 \bigr)^{\alpha_D},
\]
which is (ACT3).

Finally, if (ACT4) failed, a subsequence would have
\(r_n<\varepsilon^2/4-\gamma\) for some \(\gamma>0\), while the powered
term tends to zero. The displayed estimate would then give
\(\limsup_nD(\pi_n)<\varepsilon\), contradicting the assumed lower bound.
Therefore every large-carrier authentication sequence obeys the stated
three-way alternative. The argument rounds a supplied physical carrier;
it does not manufacture one or identify an unbounded payload, so it does
not close the root.
