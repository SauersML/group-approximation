---
rg: 2
id: kms-hb2-groups-contain-genus-two-surface-subgroups-proof
kind: route
title: One integer-labelled 24-chamber girth surface has trivial vertex words in the integral vertex groups, so it is a girth surface for G_HB2(p) at every odd prime
target: kms-hb2-groups-contain-genus-two-surface-subgroups
requires: [kms-hb2-girth-surfaces-give-surface-subgroups, cckw-kms-triangle-groups-structure]
artifacts:
  - experiments/kms-hb2-surface-subgroups/surface67-integer-labels.json
  - experiments/kms-hb2-surface-subgroups/verify_integer_certificate.py
  - experiments/kms-hb2-surface-subgroups/verify.log
  - experiments/ghb7-girth-surfaces/certificates-genus2.json
---

## The certificate

`experiments/kms-hb2-surface-subgroups/surface67-integer-labels.json` has `T = 24`. Its involutions
`r_0, r_1, r_2` are those of surface 67 in `experiments/ghb7-girth-surfaces/certificates-genus2.json`.
It lists one label `[k, t, s, x]` for every side, where `t < s = r_k(t)` and `x` is an integer.
- Crossing from `t` to `s` multiplies by `g_k^x`; crossing back multiplies by `g_k^{−x}`.
- The labels are the `F_7` labels of that certificate, lifted to `{−3, …, 3}`. All of them lie in
  `{−1, 1, 2}`.

## Verification

`verify_integer_certificate.py` shares no code with the search or with the `F_7` verifier. Its output
is `verify.log`, ALL PASS:
1. each `r_k` is a fixed-point-free involution, and `<r_0, r_1, r_2>` is transitive;
2. every alternating `<r_j, r_k>` walk closes after exactly 6, 8, 8 distinct chambers;
3. the chamber graph is bipartite, so `S` is orientable, and `V − E + F = 10 − 36 + 24 = −2`;
4. each of the 36 sides carries one nonzero integer label, and the only prime dividing a label is 2;
5. all 72 vertex words are the identity in the integral groups
   `N_3 = <a,b | [a,b,a], [a,b,b]>` (type 0) and `N_4^{xy} = <x,y | [x,y,x], [x,y,y,x], [x,y,y,y]>`
   with `(x,y) = (c,b)` (type 1) and `(c,a)` (type 2), computed with explicit normal-form laws;
6. the same 72 words map to `I` under `ψ` over `Z` (cross-check);
7. `ψ(a), ψ(b), ψ(c)` satisfy the eight commutator relators over `Z`;
8. the normal-form laws are group laws satisfying the relators with `u = [x,y]`, `v = [u,y]`.

## The normal-form laws model the integral vertex groups

Take `N_4^{xy}`. The argument for `N_3` is the same, with `v` omitted.
- The argument of Step 0(a) of `kms-hb2-girth-surfaces-give-surface-subgroups-proof` uses no `p`-th
  powers. So every element of `N_4^{xy}` is `y^β x^γ u^μ v^ν`.
- The law in the verifier, on quadruples `(β, γ, μ, ν)`, is the semidirect product `Z^3 ⋊ Z`, where the
  generator of `Z` acts on `(x, u, v)` by `x ↦ xu`, `u ↦ uv`, `v ↦ v`. The verifier checks associativity
  and inverses on random triples.
- In this group `X = (0,1,0,0)` and `Y = (1,0,0,0)` satisfy the relators, with `[X,Y] = (0,0,1,0)` and
  `[[X,Y],Y] = (0,0,0,1)` (item 8).
- So `x ↦ X`, `y ↦ Y` extends to a homomorphism sending `y^β x^γ u^μ v^ν` to
  `Y^β X^γ U^μ V^ν = (β, γ, μ, ν)`. It is injective on normal forms, hence an isomorphism.
- So a word that is the identity under the law is `1` in `N_4^{xy}`.

Item 6 gives this independently: by the entries in Step 0(c), read over `Z` with no division, `ψ` is
injective on the normal forms of `N_3` and `N_4^{xy}`.

## Deduction for a fixed odd prime `p`

- Every label lies in `{−1, 1, 2}`, so none is divisible by `p`.
- Adding `a^p, b^p` (respectively `x^p, y^p`) gives surjections `N_3 → U^{ab}` and
  `N_4^{xy} → U^{xy}` onto the vertex groups of Step 0 of the criterion proof. These map on to
  `X_0, X_1, X_2 ≤ G`.
- So every vertex word of the certificate is `1` in `G`. The certificate is a girth surface of size 24
  for `G = G_{HB_2^{(2)}}(p)` in the sense of `kms-hb2-girth-surfaces-give-surface-subgroups`.
- `S` is orientable with `χ(S) = −24/12 = −2`. So the criterion gives an injective homomorphism from the
  genus-2 surface group onto a quasiconvex subgroup of `G`.
