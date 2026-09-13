---
rg: 2
id: kt-sofic-monomial-commutant-core-is-normalized
kind: claim
title: For a sofic model, Kun--Thom 4.1 normalizes the monomial core of the von Neumann Gamma-commutant
distinct_from:
  kun-thom-sofic-centralizer-normalization: that normalizes the permutation centralizer inside the universal sofic group; this transports it into the matrix ultraproduct, adds the invariant diagonal, and normalizes the von Neumann algebra they generate.
  kt-sofic-models-normalize-vn-commutants: that is the open statement that the whole von Neumann Gamma-commutant of a sofic model is normalized; this proves normalization on the monomial core only and shows a witness against the open statement can be taken off that core.
---

**ESTABLISHED.** Let `Gamma < G` be infranormal with `Gamma` and `G` Kazhdan.
Let `sigma : G -> S_U` be an injective sofic representation with canonical
trace. Realize `S_U` by permutation matrices in `M = prod_U M_n`, and write
`D = prod_U D_n` for the diagonal. Put

```text
R       = sigma(Gamma)' cap M,
N_sigma = ( C_(S_U)(sigma(Gamma))  union  (D cap R) )''   inside M.
```

1. **Monomial core.** A monomial unitary of `M` (a permutation times a
   diagonal unitary) commutes with `sigma(Gamma)` exactly when its permutation
   part lies in `C_(S_U)(sigma(Gamma))` and its diagonal part in `D cap R`.
   So every such unitary lies in `N_sigma`, and `N_sigma <= R`.
2. **Normalization of the core.** `sigma(G)` normalizes `N_sigma`.
3. **Witnesses live off the core.** If `z in R` and `sigma(g) z sigma(g)^* notin R`
   for some `g in G`, then `z - E_(N_sigma)(z)` lies in `R` and is orthogonal to
   `N_sigma`, and it has the same property.

Consequently, in a sofic model any failure of normalization of the von
Neumann `Gamma`-commutant, which by
`rigid-compression-defect-normalization-dichotomy` would already answer
Question 3.4 negatively, is carried by commutant elements orthogonal to every
monomial unitary commuting with `sigma(Gamma)`. What Kun--Thom's permutation
calculus controls in the matrix ultraproduct is exactly `N_sigma`.

Model tests. For `Gamma` normal the statement is trivially true. For a
one-compressor subgroup `<Gamma, t>`, which is not Kazhdan, item 2 fails already
for permutations (`kun-thom-single-compressor-sofic-joint-nonsofic`), so the
Kazhdan hypothesis on `G` is load-bearing.

Derivation: `kt-sofic-monomial-commutant-core-is-normalized-proof`.
