---
rg: 2
id: corona-traces-separate-paradox-measure-proof
kind: route
title: "No MF quotient kills every corona trace; ultraproduct embeddings give LEF; on subshift rings MF, LEF and corona traces coincide"
target: corona-traces-separate-paradox-from-measure-for-el-n
requires:
  - stably-infinite-ring-elementary-groups-have-no-mf-quotient
  - lef-group-canonical-trace-is-a-corona-trace
  - subshift-elementary-mf-iff-word-edges-lie-on-cycles
  - elementary-group-trace-amenable-iff-ring-residually-finite
---

- **(i)** By `stably-infinite-ring-elementary-groups-have-no-mf-quotient`, every homomorphism from EL_N(R)
  to an MF group is trivial. By manuscript Lemma `prop:mf-residual-calculus`, quoted verbatim in the
  artifact source ("Every homomorphism from G to an MF group is trivial on K if and only if every corona
  homomorphism from G is trivial on K"), every corona homomorphism is trivial. For a unital *-homomorphism Φ
  into a corona, Φ(u_g) = 1 for all g, so tr_ω∘Φ(u_g) = 1 and tr_ω∘Φ is the trivial character. For R ≠ 0,
  EL_N(R) ≠ 1, so the canonical trace differs from it.
- **(ii)** The unital embedding induces an injective homomorphism GL_N(R) → ∏_ω GL_{N N_k}(F_{q_k}), an
  algebraic ultraproduct of finite groups. A countable subgroup of such an ultraproduct is LEF: finitely many
  products and inequalities hold in ω-many coordinates (Pestov artifact §3.3). Now apply (b) of
  `lef-group-canonical-trace-is-a-corona-trace`.
- **(iii)** MF ⟹ LEF ⟺ R_X directly finite by `subshift-elementary-mf-iff-word-edges-lie-on-cycles`.
  LEF ⟹ corona trace ⟹ MF by (b) and (a) of `lef-group-canonical-trace-is-a-corona-trace`.
- **(iv)** This is Corollary A of `elementary-group-trace-amenable-iff-ring-residually-finite`. ∎

Full text: `research/artifacts/un-traces-2026-09-13-part1.md` §5.
