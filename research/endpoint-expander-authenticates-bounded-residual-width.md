---
rg: 2
id: endpoint-expander-authenticates-bounded-residual-width
kind: claim
title: Irreducible endpoint expansion authenticates supplied bounded residual factors
artifacts:
  - research/tfd-expectation-untwists-and-rounds-residual-generators.md
distinct_from:
  bounded-payload-congruence-tensors-have-uniform-capture: that assumes exact tensor blocks; this derives those tensor blocks from a supplied congruence factor and finite commutator tests.
  approximate-central-tensor-coverage-forces-capture: that rounds a supplied almost-reducing physical carrier but assumes its corner is already near the tensor hull; this proves that nearness once the endpoint factor and its block carrier are supplied.
  quantum-expander-relative-commutant-rounding: that starts from an abstract expander channel and stops at a commutant; this uses property TFD uniformly over every finite-dimensional endpoint, then rounds the residual matrices to exact modular-vertex representations.
---

Let \(\mathcal H_D\) denote the bounded-payload congruence tensor hull of
**bounded-payload-congruence-tensors-have-uniform-capture**. For an exact
modular-vertex pair \(\pi\), define its residual payload width at tolerance
\(\delta\) by
\[
 w_\delta(\pi)=
 \min\{D:\operatorname{dist}_2(\pi,\mathcal H_D)\leq\delta\},             \tag{ERW1}
\]
with value \(+\infty\) if the set is empty. This definition minimizes after
absorbing every compatible congruence endpoint factor; in particular the
Steinberg endpoints have \(w_0=1\).

Fix a finite-dimensional Kazhdan pair \((Q,\kappa)\) for
\[
 A=\operatorname{PSL}_2(\mathbb Z[1/2])
\]
coming from property \((T;FD)\). Suppose an exact vertex pair has a supplied
common orthogonal block decomposition
\[
 H=\bigoplus_j\bigl(\mathbb C^{k_j}\otimes H_{\eta_j}\bigr),
 \qquad k_j\leq D,                                      \tag{ERW2}
\]
where every
\[
 \eta_j:A\longrightarrow U(H_{\eta_j})
\]
is an irreducible finite-dimensional congruence endpoint. For a torsion
generator \(s\in\{x,a\}\) in vertex \(\epsilon\in\{+,-\}\), put
\[
 Y_{\epsilon,j,s}
 =\pi_{\epsilon,j}(s)
  \bigl(1_{k_j}\otimes\eta_{j,\epsilon}(s)^*\bigr).       \tag{ERW3}
\]
With \(w_j=\dim(H_j)/\dim(H)\), define the endpoint-factor authentication
energy
\[
 \Xi^2=
 \sum_jw_j\sum_{\epsilon,s}\sum_{g\in Q}
 \bigl\|[Y_{\epsilon,j,s},
  1_{k_j}\otimes\eta_j(g)]\bigr\|_{2,H_j}^2.             \tag{ERW4}
\]

There are exact modular-vertex payloads
\[
 \kappa_{j,\epsilon}:V_\epsilon\longrightarrow U(k_j)
\]
such that
\[
 \widehat\pi_\epsilon
 =\bigoplus_j
  \bigl(\kappa_{j,\epsilon}\otimes\eta_{j,\epsilon}\bigr)
 \in\mathcal H_D                                      \tag{ERW5}
\]
and
\[
 d_2(\pi,\widehat\pi)\leq C_\kappa\Xi.                   \tag{ERW6}
\]
The constant is independent of all congruence levels, endpoint dimensions,
multiplicities, and the number of blocks. Consequently
\[
 D(\pi)\leq
 C_{D,\kappa}
 \bigl(\operatorname{def}(\pi)+\Xi\bigr)^{\alpha_D}.     \tag{ERW7}
\]
In particular,
\[
 w_{C_\kappa\Xi}(\pi)\leq D.                             \tag{ERW8}
\]

Thus property \((T;FD)\) eliminates collapse of the endpoint adjoint gap
for a supplied irreducible factor as a possible escape. For a positive-distance sequence, every fixed-\(D\)
candidate decomposition (ERW2) must have authentication energy bounded away
from zero, unless positive physical rank is left outside the decomposition.
Combined with **approximate-central-tensor-coverage-forces-capture**, the
genuinely noncongruence alternative is now exact: failure to discover
almost-central endpoint-factor carriers, or unbounded residual width after
all such factors are absorbed. The theorem does not discover the factors,
so the root remains open.

DERIVATION
tfd-expectation-untwists-and-rounds-residual-generators
