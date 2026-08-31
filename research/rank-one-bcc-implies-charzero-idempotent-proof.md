---
rg: 2
id: rank-one-bcc-implies-charzero-idempotent-proof
kind: route
title: Pass from rank-one Baum--Connes to algebraic idempotent vanishing
target: rank-one-lattice-kadison-kaplansky-and-charzero-idempotents
requires:
  - real-rank-one-lattices-bcc-finite-wreath-products
---

By [[real-rank-one-lattices-bcc-finite-wreath-products]], `Gamma`
satisfies Baum--Connes with coefficients, hence ordinary Baum--Connes and
in particular surjectivity of its assembly map. For a torsion-free group,
Baum--Connes surjectivity implies the Kadison--Kaplansky conjecture.
Nishikawa--Petrosyan recall this implication in Section 2.1 of
*Dehn fillings, equivariant homology, and the Baum--Connes conjecture*,
arXiv:2509.15070v2, citing Gomez Aparicio--Julg--Valette,
Proposition 4.20. Therefore `C_r^*(Gamma)` has no nontrivial idempotent.

It remains to justify the stated all-characteristic-zero algebraic
consequence. Suppose that `p in k[Gamma]` is a nontrivial idempotent.
Only finitely many coefficients of `p` occur. They generate a finitely
generated subfield `k_0` of `k` over `Q`. Every finitely generated
field of characteristic zero embeds in `C`; choose an embedding
`i:k_0 -> C`. Applying `i` coefficientwise gives a nontrivial
idempotent in `C[Gamma]`: injectivity of `i` preserves a coefficient
witnessing `p != 0,1`.

Finally, the left regular representation embeds `C[Gamma]` faithfully
in `C_r^*(Gamma)` (apply an element to the delta function at the
identity to recover all coefficients). This contradicts
Kadison--Kaplansky. Hence no such `p` exists. QED

The torsion-free hypothesis is essential to this implication and is not
silently dropped.
Checked 2026-08-31:
https://arxiv.org/abs/2509.15070
