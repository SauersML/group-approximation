# Zero-literature audit of the tensor-synchronized rope

**Audited claim:** `regular-mf-tensor-synchronized-rope-2026-08-25.md`  
**Conclusion:** the tensor construction proves a faithful regular model of the
vertex group and exact edge compatibility, but it does **not** by itself prove
that the HNN group is MF.  The remaining implication is precisely a
compatible-amalgam/free-product MF permanence theorem. The repository does
not prove that theorem internally. It is exactly Shulman's
arXiv:2603.13564v2, Theorem 20; the external-theorem completion, including
faithful corner embeddings and group faithfulness, is recorded in
`regular-mf-tensor-sync-shulman-completion-2026-08-26.md`.

## 1. What the tensor construction really proves

Write (G=\Gamma\times Q), with edge maps

\[
\iota _0(s)=(s,1),\qquad \iota _1(s)=(s,\tau(s)).
\]

The finite kernel condition proves that the two finite edge images are
isomorphic.  Their restrictions inside the left regular representation of
(G_n) are equal multiples of the same regular representation, hence admit an
exact intertwiner (W_n).  Therefore the formulas in the artifact give

\[
  V:G\longrightarrow U(E),\qquad W\in U(E),\qquad
  WV(\iota _0(s))W^*=V(\iota _1(s)).
\]

The ultralimit trace calculation is valid and gives

\[
  T(V(g,q))=\delta_{(g,q),(1,1)}.
\]

Consequently (V) is injective.  The local limsup/direct-sum argument also
does prove, from first principles, that

\[
  D'=C^*(V(G),W)
\]

is MF: a finite family of quotient norms can be lower-witnessed by finitely
many late coordinates, all upper estimates hold on a common tail, finite
direct sums of the coordinate algebras are MF, and diagonalization gives a
matrix-corona embedding.

Thus Sections 1--2 produce an MF algebra containing a faithful regular copy of
the **vertex group** and one unitary satisfying the edge equations.

## 2. The compatible unitary need not represent the HNN faithfully

The universal property gives a homomorphism

\[
  G*_{\iota_0\sim\iota_1}
     \longrightarrow U(D'),\qquad g\mapsto V(g),\quad t\mapsto W,
\]

but there is no reason for it to be injective.

The smallest counterexample is

\[
  \Gamma=Q=S=1.
\]

All hypotheses of the tensor construction hold, every (G_n) is trivial, and
one may take (W_n=1).  The HNN group is (\mathbb Z), while the constructed
map sends its generator to (1).  More generally, with (S=1) the construction
can send the stable letter of (G*\mathbb Z) to (1).

Therefore “(D') is MF and contains an exact compatible edge unitary” is not
the desired injective matrix-corona representation.

## 3. The exact missing MF theorem

Let

\[
  D=C^*(V(G)),\quad B_0=C^*(V(\iota_0(S))),\quad
  B_1=C^*(V(\iota_1(S))),\quad \alpha=\operatorname{Ad}(W)|_{B_0}.
\]

The single theorem that would close the MF step is:

> **Compatible-corona HNN permanence.**  If (D) is separable and there is a
> faithful embedding (j:D\to\mathcal Q_{\mathbf d}) together with a unitary
> (w\in\mathcal Q_{\mathbf d}) satisfying
> \(w j(b)w^*=j(\alpha(b))\) for every (b\in B_0), then the universal
> C-star HNN algebra (\operatorname{HNN}(D,B_0,\alpha)) is MF.

The artifact obtains exactly the hypothesis by first embedding (D') into a
matrix corona.  It does not prove the displayed theorem.  Its Section 3 invokes
two external results to obtain it:

1. the identification of the universal HNN algebra with the (e_{11})-corner
   of
   \[
     M_2(D)*_{B_0\oplus B_1}M_2(B_0);
   \]
2. the theorem that a full amalgamated free product is MF when its two factors
   have compatible faithful embeddings into one matrix corona.

The second item is the essential gap.  Agreement of two embeddings on the
amalgam only gives a generally nonfaithful map from the universal amalgam into
the corona.  It does not prove that the universal amalgam is MF.  At
(B_0=\mathbb C1), compatible-HNN permanence already contains MF permanence
for the free product (D*C^*(\mathbb Z)), so it cannot be replaced by the
elementary fact that subalgebras of a matrix corona are MF.

Repository search finds no internal proof of this permanence theorem.  The
existing `SymmetricDoubleShulman.lean` boundary explicitly says that it does
not construct the required matrix models and exposes the MF conclusion as a
hypothesis.  Hence the rope endpoint is conditional under the requested
zero-literature policy.

## 4. The corner calculation is not the hard part

The first external item can plausibly be replaced by a short universal-property
proof.  In

\[
  P=M_2(D)*_{B_0\oplus B_1}M_2(B_0),
\]

let (x_{ij}) and (y_{ij}) denote the matrix units from the first and second
factors, whose diagonal projections are identified, and put (p=x_{11}=y_{11}).
Then

\[
  u=x_{12}y_{21}\in pPp
\]

is unitary in the corner.  The amalgamation rule

\[
  \operatorname{diag}(b_0,b_1)
  =\operatorname{diag}(b_0,\alpha(b_1))
\]

between the two factors gives

\[
  ubu^*=\alpha(b)\qquad(b\in B_0).
\]

The two universal properties then construct mutually inverse maps between
(pPp) and the universal HNN algebra.  This is finite matrix-unit bookkeeping;
it does not supply MF of (P).  The compatible-amalgam MF theorem remains.

## 5. The group-faithfulness/regular-trace step has a self-contained repair

The artifact invokes a reduced von Neumann HNN normal form.  That input is
unnecessary.

Let (\pi_T) be the GNS representation of (D) for (T).  Since

\[
  \langle V(g)\xi,V(h)\xi\rangle
   =T(V(h^{-1}g))=\delta_{g,h},
\]

the GNS representation restricted to the group generators is the left regular
representation (\lambda_G).  If (H) is the abstract group HNN extension,
then (\lambda_H|_G) is a direct sum of copies of (\lambda_G), by decomposing
(H) into left (G)-cosets.  Hence it extends from the generators to a
representation

\[
  \widetilde\pi_T:D\longrightarrow B(\ell^2 H)
\]

with (\widetilde\pi_T(V(g))=\lambda_H(g)).

The unitary (\lambda_H(t)) implements (\alpha) on (B_0), first on the
group generators and then by norm continuity.  The universal property of the
C-star HNN algebra therefore gives a representation sending every canonical
group unitary to (\lambda_H(h)).  Since

\[
  \lambda_H(h)\delta_1=\delta_h,
\]

the canonical group map is injective.  The vector trace at (\delta_1) is the
regular character.  This replaces the conditional expectations, reduced von
Neumann HNN construction, and reduced-HNN moment formula by elementary group
regular representation theory.

## 6. Minimal repair obligation

After the preceding repair, the sole substantive open obligation is one of the
following equivalent-strength deliverables:

- prove compatible-corona HNN permanence directly by finite matrix models; or
- prove the compatible-corona amalgamated-free-product MF theorem and combine
  it with the explicit (2\times2) corner calculation.

A direct matrix proof must add a relative Britton-separation lemma: after an
amplification, choose an edge intertwiner that both preserves the edge
relations and keeps every prescribed reduced alternating word uniformly away
from zero.  The particular (W_n) constructed from the finite regular edge
images supplies compatibility only; it supplies no such freeness or norm
separation.  Establishing that lemma is exactly the missing analytic content,
not bookkeeping already present in the tensor model.

No status label should be upgraded from the present artifact under a
zero-literature audit. With the source-verified Shulman theorem admitted, the
completion artifact discharges the obligation unconditionally in the ordinary
literature-relative sense.
