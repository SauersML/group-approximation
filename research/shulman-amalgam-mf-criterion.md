---
rg: 2
id: shulman-amalgam-mf-criterion
kind: claim
title: Shulman's necessary and sufficient condition for MF amalgams
distinct_from:
  symmetric-double-weak-mf: That claim is this repository's application of Shulman's symmetric Theorem 10 to doubles of residually finite groups; this one imports the general Theorem 16 for non-symmetric amalgams, which the symmetric theorem does not contain.
  central-extension-twisted-sector-criterion: That criterion is about central order-two extensions and is internal; this one is a published statement about amalgamated free products.
artifacts:
  - research/artifacts/shulman-2603-13564-verified.md
---

**PRIMARY-SOURCE FIREWALL (operator norm only).** The current arXiv version is
[arXiv:2603.13564v2](https://arxiv.org/html/2603.13564v2), revised
22 March 2026 (v1 was submitted 13 March 2026). In the paper's convention,
\(A *_C A\) always uses the **same** inclusion \(C\hookrightarrow A\) in the
two copies. No amenability, finite dimensionality, or relative property
assumption is placed on \(C\). Thus Theorem 10 applies unchanged when the
edge algebra comes from a nonamenable or property-\((T)\) subgroup.

Shulman, *The MF property for amalgamated free products*, arXiv:2603.13564v2,
**Theorem 16** (v2 body numbering; verbatim in the artifact): for separable C*-algebras
`A, B, C` with inclusions `theta_A : C -> A` and `theta_B : C -> B`, the
amalgam `A *_C B` is MF **if and only if** there are embeddings
`phi_A : A -> prod M_n / (+) M_n` and `phi_B : B -> prod M_n / (+) M_n` with
`phi_A o theta_A = phi_B o theta_B`.

**Theorem 10** is the symmetric case: `A *_C A` is MF whenever `A` is
separable MF and `C <= A` is any C*-subalgebra.

Group bridge, also from the paper:
`C*(G_1 *_H G_2) = C*(G_1) *_{C*(H)} C*(G_2)`. Its introduction states
the separate group-level corollary that if \(G\) is an MF group, then
\(G *_H G\) is MF for every subgroup \(H\leq G\). Here group MF means
embedding in the unitary group of the **operator-norm** matrix corona.
This conclusion neither chooses the canonical group trace nor supplies
normalized-Hilbert--Schmidt microstates. In particular, it is not a
hyperlinear permanence theorem; the general implication from this weak
group-MF convention to hyperlinearity remains open in this Cairn.

For a genuinely asymmetric amalgam, Theorem 16 is the exact operator-norm
frontier: MF is equivalent to finding matrix-corona embeddings of the two
vertex algebras whose restrictions agree **exactly** on the edge algebra.
Accordingly, after an MF symmetric double has been recognized, changing the
edge from amenable to nonamenable or Kazhdan cannot make that same double
non-MF. Any operator-MF obstruction must instead be asymmetric or violate the
common-corona compatibility condition. A nonhyperlinearity argument still
has to obstruct the canonical trace separately.

**Trust surface.**  Source-verified from the PDF this session; the
transcription is in the artifact. The v2 introduction's "Th. 20" forward
reference is stale. Scope caution: Theorem 16 concerns
C*-algebras, and MF of `C*(G)` is strictly stronger than group MF in the
convention used here, so a route built on it must also carry MF of both
vertex algebras.
