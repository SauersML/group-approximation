---
rg: 2
id: bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test
kind: claim
title: Gapped spectral projections supported on an a-T-menable subgroup of a Kun--Thom actor pass the trace test
distinct_from:
  kun-thom-actor-algebraic-idempotents-pass-trace-test: that covers algebraic idempotents of M_n(C[G]) through congruence quotients; this covers non-algebraic gapped spectral projections of infinite-spectrum elements, but only those supported on a subgroup with surjective assembly, through Lück's theorem and Higson--Kasparov.
  bc-kun-thom-gap-label-is-congruence-eigenvalue-limit: that writes the trace of any gapped projection as a congruence eigenvalue-fraction limit, with no arithmetic conclusion; this proves membership in Z[1/P] for a subclass defined by the support.
  a-t-menable-groups-have-no-rigid-compression-defect: that concerns compression defects of a-T-menable hosts; this concerns reduced-algebra traces of projections supported on a-T-menable subgroups.
artifacts:
  - research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md
---

**ESTABLISHED** (imports (I1) and (I2) below, quoted from the extracted source text).

Let `G = EL_r(F_q[x_1^(+-1), ..., x_d^(+-1)]) semidirect SL_d(Z)`, with `r, d >= 3`, be a
Kun--Thom Theorem E actor, and let `P = P(q,r,d)`. Let `H <= G` be a subgroup whose degree-0
assembly map `A_FIN : K_0^H(E_FIN H) -> K_0(C*_r H)` is surjective. This holds for every
a-T-menable `H`. Let `a = a* ∈ M_n(C[H])`, and let `c` lie in a gap of the spectrum of
`lambda(a)`. Then

```text
tau( chi_((-inf,c))(lambda(a)) )  ∈  Lambda^H  ⊆  Z[1/P].
```

**Imports.** Lück--Reich, arXiv:math/0402405, extracted with `pdftotext` on MSI:
- **(I1)** Theorem 3.22, proved in Lück, Invent. Math. 149 (2002), Theorem 0.3. The image of
  `tr ∘ (A_FIN ⊗ id)` on `K_0^G(E_FIN G) ⊗ Lambda^G` is `Lambda^G`.
- **(I2)** Theorem 5.1, Higson--Kasparov. a-T-menable discrete groups satisfy Baum--Connes with
  coefficients, and hence Baum--Connes. The survey's example list covers countable amenable
  groups and countable groups acting properly on trees or products of trees, and the class is
  closed under subgroups and finite products.

See `research/artifacts/bc-gap-label-subgroup-support-2026-09-12.md`, Section 2, for the
verbatim quotes.

**Supports ruled out on the actor** (artifact, Section 3):
- the Borel and unipotent subgroups of `EL_r(R)`;
- the lamplighters `F_q wr Z^k`;
- the corner blocks `E_2(F_q[x_1^(+-1)])`, which act properly on products of two Bruhat--Tits
  trees;
- the corner block `SL_2(Z)` of `SL_d(Z)`;
- finite products of these.

**Consequence.** A projection refuting the trace test on a Theorem E actor must be a gapped
spectral projection of an element whose support generates a subgroup lying in no subgroup with
surjective assembly. In particular that subgroup is not a-T-menable. The computable test
operators (lamplighter Markov operators, Borel-supported elements, tree-group Laplacians) cannot
refute.
