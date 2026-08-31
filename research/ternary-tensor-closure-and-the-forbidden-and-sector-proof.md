---
rg: 2
id: ternary-tensor-closure-and-the-forbidden-and-sector-proof
kind: route
title: Tensor three marked extensions to manufacture the forbidden atom
target: central-character-extension-profiles-are-affine-under-odd-tensor-products
requires:
  - perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model
---

# Tensor three marked extensions to manufacture the forbidden atom

## 1. Exact ternary closure

Let \(\epsilon,\eta,\theta\in\mathsf E_\zeta\), witnessed by nonzero
unitary representations

\[
 \pi_\epsilon:\Gamma\to\mathcal U(H_\epsilon),\qquad
 \pi_\eta:\Gamma\to\mathcal U(H_\eta),\qquad
 \pi_\theta:\Gamma\to\mathcal U(H_\theta).
 \tag{1}
\]

The conjugate representation is

\[
 \overline{\pi_\theta}(g)
 =\overline{\pi_\theta(g)}
 \quad\text{on }\overline{H_\theta}.
 \tag{2}
\]

Define the diagonal tensor-product representation

\[
 \Pi(g)=
 \pi_\epsilon(g)\otimes
 \pi_\eta(g)\otimes
 \overline{\pi_\theta(g)}.
 \tag{3}
\]

For \(z\in Z\),

\[
 \Pi(z)=
 \zeta(z)\zeta(z)\overline{\zeta(z)}\,I
 =\zeta(z)I.
 \tag{4}
\]

The port values are real signs, so conjugation does not change them:

\[
 \Pi(r_i)=\epsilon_i\eta_i\theta_i I.
 \tag{5}
\]

Thus

\[
 \epsilon,\eta,\theta\in\mathsf E_\zeta
 \quad\Longrightarrow\quad
 \epsilon\eta\theta\in\mathsf E_\zeta.
 \tag{6}
\]

No commutation assumption on the \(r_i\), finiteness assumption on
\(\Gamma\), or structural assumption on the auxiliary generators appears
in this calculation. If the three witnesses are finite dimensional, their
tensor product is finite dimensional.

## 2. Ternary-closed Boolean sets are affine

Assume \(\mathsf E_\zeta\neq\varnothing\) and fix
\(\epsilon^0\in\mathsf E_\zeta\). Put

\[
 H=\{\epsilon\epsilon^0:\epsilon\in\mathsf E_\zeta\}
 \subseteq\{\pm1\}^k.
 \tag{7}
\]

The identity belongs to \(H\). If
\(h_1=\epsilon\epsilon^0\) and \(h_2=\eta\epsilon^0\), then (6), applied
to \(\epsilon,\eta,\epsilon^0\), gives
\(\epsilon\eta\epsilon^0\in\mathsf E_\zeta\). Hence

\[
 h_1h_2
 =\epsilon\eta
 =(\epsilon\eta\epsilon^0)\epsilon^0
 \in H.
 \tag{8}
\]

Every element of the Boolean sign group is its own inverse, so \(H\) is a
subgroup and

\[
 \mathsf E_\zeta=\epsilon^0H.
 \tag{9}
\]

Under \(\epsilon_i=(-1)^{x_i}\), subgroups are linear
\(\mathbf F_2\)-subspaces and their cosets are affine subspaces. This
proves the classification.

The argument works for a central subgroup of any order. Only the ports
are Boolean; the conjugate factor in (3) is exactly what returns an
arbitrary central character \(\zeta\), rather than requiring
\(\zeta^2=1\).

## 3. Minimal NAND/orthogonality obstruction

For two ports, let the witnesses for the three allowed patterns be

\[
 \pi_{00}:(+,+),\qquad
 \pi_{10}:(-,+),\qquad
 \pi_{01}:(+,-).
 \tag{10}
\]

Then

\[
 \Pi=\pi_{10}\otimes\pi_{01}\otimes\overline{\pi_{00}}
 \tag{11}
\]

has central character \(\zeta\) and port pattern

\[
 (-,+)(+,-)(+,+)=(-,-).
 \tag{12}
\]

If \(P=(1-r)/2\) and \(Q=(1-s)/2\), the three patterns in (10) are exactly
the scalar sectors on which \(PQ=0\), while (12) has \(P=Q=1\). Therefore
no ordinary-group extension profile can be exactly the truth set of the
orthogonality relation.

This also explains the residual Clifford sector in controlled-Pauli
dilations. On the forbidden atom, tensor products place an inverse
projective multiplier in the auxiliary multiplicity space. Its
anticommutation cancels the Pauli-frame anticommutation, producing an
honest representation of every ordinary group relator. Adding more
ordinary auxiliary relators cannot remove the tensor representation in
(11), because (11) is constructed after the full group has already been
presented.

## 4. Normalized-Hilbert--Schmidt closure

Let a finite presentation of \(\Gamma\) be fixed and suppose
\(\sigma_j\) are unitary maps on its generators. Their diagonal tensor
map \(\Sigma=\sigma_1\otimes\sigma_2\otimes\overline{\sigma_3}\) satisfies,
for every relator word \(w\),

\[
 \Sigma(w)=
 \sigma_1(w)\otimes\sigma_2(w)\otimes
 \overline{\sigma_3(w)}.
 \tag{13}
\]

For unitaries \(A,B,C\), normalized Hilbert--Schmidt norm gives

\[
 \|A\otimes B\otimes C-I\|_2
 \leq
 \|A-I\|_2+\|B-I\|_2+\|C-I\|_2.
 \tag{14}
\]

Indeed telescope the left side into

\[
 (A-I)\otimes B\otimes C
 +I\otimes(B-I)\otimes C
 +I\otimes I\otimes(C-I),
 \tag{15}
\]

and use invariance of normalized Hilbert--Schmidt norm under tensoring
with unitaries. The same estimate applies to the defect of a port from
its target scalar sign. Consequently, three \(\delta\)-extensions of the
patterns in (10) give a \(3\delta\)-extension of (12), with matrix
dimension equal to the product of the three dimensions.

Thus even an approximate local compiler cannot have all of the following:

1. vanishing-defect extensions of the three allowed atoms;
2. one common central-character mark;
3. a dimension-independent positive defect lower bound for the forbidden
   atom.

The statement remains true if the three allowed sequences use unrelated
dimensions or unrelated auxiliary realizations.

## 5. Boundary for the perfect-qc BCS

The independent-set/SynchBCS algebra has relations

\[
 P_{i,u}P_{j,v}=0
 \tag{16}
\]

for forbidden pairs. A compiler which represents every
\(P_{i,u}\) as \((1-r_{i,u})/2\) for a group word and extends local
deterministic atoms representation-functorially meets the hypotheses of
Section 3. Its forbidden atom is forced by (11), so it cannot define a
unital copy of the BCS algebra in the marked group-word sector or provide
a robust soundness decoder.

The theorem does not rule out the remaining non-character possibilities:

- a source projection represented by a genuine Hecke sum or a selected
  matrix-corner projection rather than the sign of one group word;
- a whole-source construction in which the three local deterministic
  atoms in (10) do not separately extend;
- a one-sided trace-GNS extension whose return is not functorial on all
  representations.

These are exactly the signed-Hecke/nontransport and proper-corner gates
already isolated elsewhere in the repository. The theorem closes the
universal involution, Coxeter, Clifford, Halmos, and word-dilation branches
without any amenability, residual-finiteness, or property-(T) caveat.
