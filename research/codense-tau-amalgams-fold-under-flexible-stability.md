---
rg: 2
id: codense-tau-amalgams-fold-under-flexible-stability
kind: claim
title: Flexibly stable vertex groups and a tau-gap edge group fold every sofic approximation of an amalgam across the profinite closure of the edge group
distinct_from:
  hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable: that corrects the stable letter of one HNN extension over SL2(Z) by an isoperimetric argument; this folds the two vertex copies of an arbitrary amalgam through a swap vector, for every element of the profinite closure of the edge group.
  codense-tau-coset-soficity-forces-permutation-instability: that concerns the set action A on A/C; this concerns the group A *_C A, whose nonsoficity implies nonsoficity of that action through sofic-coset-action-makes-amalgam-double-sofic.
  sl3-arithmetic-double-finite-representations-fold: that folds exact finite-dimensional unitary representations of one arithmetic double; this folds asymptotic permutation models of any amalgam once the vertex groups are flexibly stable.
  kt-pair-group-double-is-nonsofic: that is unconditional nonsoficity from an infranormal Kazhdan edge group; this is conditional on flexible stability and uses neither property (T) nor compression of the edge group.
---

**ESTABLISHED** through a direct proof. Not independently reviewed; no
priority is claimed.

## Setting

Let `A_0, A_1` be countable groups, `H` a group with injective homomorphisms
`iota_j : H -> A_j`, and `S` a finite symmetric generating set of `H`. Put

```text
P = A_0 *_H A_1,        i_j : A_j -> P,        i_0 iota_0 = i_1 iota_1,
Delta     = { (iota_0(h), iota_1(h)) : h in H }  <=  A_0 x A_1,
Delta_bar = { g in A_0 x A_1 : g in Delta N for every finite-index normal N of A_0 x A_1 }.
```

For permutations `alpha, beta` of a finite set `U`, write
`d_U(alpha, beta) = |{u : alpha u != beta u}| / |U|`.

## Hypotheses

- **(FS)** `A_0` and `A_1` are flexibly stable in the sense of Bowen--Burton
  (arXiv:1906.02172): every sofic approximation is conjugate to a perfect
  one. Their conjugacy allows injections into finite sets `U_n` whose
  proportion of added points tends to zero. A finitely presented group that
  is flexibly P-stable in the sense of Becker--Lubotzky (arXiv:1809.00632,
  subsection "A flexible variant of P-stability") has this property.
- **(tau-Delta)** There is `kappa > 0` with the following property. For every
  finite set `X` with an action of `A_0 x A_1`, with permutation representation
  `lambda` on `l2(X)`, and every `eta` orthogonal to the `Delta`-fixed vectors,
  `max_{s in S} || lambda(iota_0 s, iota_1 s) eta - eta || >= kappa ||eta||`.

## Conclusions

- **(F1) Exact inequality**, using only (tau-Delta). For every finite set `U`,
  all homomorphisms `rho_j : A_j -> Sym(U)` and every `(a,b)` in `Delta_bar`,

  ```text
  d_U(rho_0(a), rho_1(b)) <= (4/kappa^2) max_{s in S} d_U(rho_0(iota_0 s), rho_1(iota_1 s)).   (FT1)
  ```

- **(F2) Fold.** Let `sigma_n : P -> Sym(V_n)` be asymptotically multiplicative,
  and suppose each vertex restriction `sigma_n o i_j` is conjugate, in
  Bowen--Burton's sense, to homomorphisms `A_j -> Sym(W_n^(j))`. Then for
  every `(a,b)` in `Delta_bar`,
  `d_{V_n}(sigma_n(i_0 a), sigma_n(i_1 b)) -> 0`.
- **(F3) Nonsoficity.** If (FS) and (tau-Delta) hold and `Delta_bar != Delta`,
  then `P` is not sofic.

## The double

Take `A_0 = A_1 = A` and let `iota_0 = iota_1` be the inclusion of `C = H <= A`.

- **The gap.** (tau-Delta) follows from **(tau-C)**: a uniform gap `kappa` for
  `C` on `l2(X)`, relative to the `C`-fixed vectors, for every finite `A`-set
  `X`.
- **The closure.** If `C` is dense in the profinite topology of `A`, then
  `Delta_bar` contains the diagonal of `A`.

So if `A` is flexibly stable, `C` is proper and profinitely dense, and (tau-C)
holds, then `A *_C A` is not sofic. Every `a` in `A \ C` gives the fold word
`i_0(a) i_1(a)^(-1) != 1`, which (F2) forces towards the identity.

By `sofic-coset-action-makes-amalgam-double-sofic`, the same hypotheses make
the set action `A` on `A/C` nonsofic. The centralizing HNN extension
`<A, t | [t, C] = 1>` contains `A *_C A` as the subgroup `<A, tAt^(-1)>`, so it
is not sofic either.

DERIVATION
codense-tau-amalgams-fold-under-flexible-stability-proof
