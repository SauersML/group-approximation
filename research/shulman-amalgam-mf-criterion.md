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
  - research/artifacts/mf-nonhyperlinear-double-separation-2026-09-20.md
---

**PRIMARY-SOURCE FIREWALL (operator norm only).** Rechecked 2026-09-20 in
[arXiv:2603.13564v3](https://arxiv.org/html/2603.13564v3), revised
31 August 2026. In the paper's convention,
\(A *_C A\) always uses the **same** inclusion \(C\hookrightarrow A\) in the
two copies. No amenability, finite dimensionality, or relative property
assumption is placed on \(C\). Thus Theorem 10 applies unchanged when the
edge algebra comes from a nonamenable or property-\((T)\) subgroup.

Shulman, *The MF property for amalgamated free products*, arXiv:2603.13564v3,
**Theorem 16** (body numbering; the introduction still says "Th. 20"):
for separable C*-algebras
`A, B, C` with inclusions `theta_A : C -> A` and `theta_B : C -> B`, the
amalgam `A *_C B` is MF **if and only if** there are embeddings
`phi_A : A -> prod M_n / (+) M_n` and `phi_B : B -> prod M_n / (+) M_n` with
`phi_A o theta_A = phi_B o theta_B`.

**Theorem 10** is the symmetric case: `A *_C A` is MF whenever `A` is
separable MF and `C <= A` is any C*-subalgebra.

Group bridge, also from the paper:
`C*(G_1 *_H G_2) = C*(G_1) *_{C*(H)} C*(G_2)`. The v3 introduction gives
the corollary with **C*(G) MF**, not merely G MF. The older wording here
conflated those hypotheses. The repository's separate
[[symmetric-double-weak-mf]] argument proves group MF for a countable
residually finite G by a faithful profinite-regular completion; it does
not assume C*(G) MF. Neither conclusion supplies canonical-trace matrix
models. Indeed [[kt-doubles-are-mf-but-not-hyperlinear]], using Jihao
Liu's analytic theorem and Andreas Thom's conditional mechanism, now
refutes the general weak group-MF to hyperlinear implication.

For a genuinely asymmetric amalgam, Theorem 16 is the exact operator-norm
frontier: MF is equivalent to finding matrix-corona embeddings of the two
vertex algebras whose restrictions agree **exactly** on the edge algebra.
Accordingly, after an MF symmetric double has been recognized, changing the
edge from amenable to nonamenable or Kazhdan cannot make that same double
non-MF. Any operator-MF obstruction must instead be asymmetric or violate the
common-corona compatibility condition. A nonhyperlinearity argument still
has to obstruct the canonical trace separately.

**Trust surface.** The original artifact transcribes the v2 PDF; the
v3 source recheck and group-interface correction are documented in
`research/artifacts/mf-nonhyperlinear-double-separation-2026-09-20.md`.
The stale "Th. 20" introduction forward reference persists in v3;
the actual theorem heading in section 3.1 is Theorem 16.
Scope caution: Theorem 16 concerns
C*-algebras, and MF of `C*(G)` is strictly stronger than group MF in the
convention used here, so a route built on it must also carry MF of both
vertex algebras.
