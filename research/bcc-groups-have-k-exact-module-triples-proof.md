---
rg: 2
id: bcc-groups-have-k-exact-module-triples-proof
kind: route
title: Naturality of assembly and half-exactness of topological K-theory, with all assembly maps isomorphisms
target: bcc-groups-have-k-exact-module-triples
requires:
  - amenable-kernel-bc-transfer-and-ktop-half-exactness
  - higson-kasparov-haagerup-satisfies-bcc
---

1. **The C*-sequence.** As in
   `k-inexact-module-triple-refutes-trivial-coefficient-bc-proof`, the Fourier--
   Gelfand transform gives `C*_r(V ⋊ G) = C(X) ⋊_r G`, `C*_r((V/W) ⋊ G) =
   C(Z) ⋊_r G` with `Z = W^perp`, and the quotient is `q = res ⋊ G` with kernel
   ideal `C_0(U) ⋊_r G`, `U = X \ Z`. So we have the `G`-equivariant short exact
   sequence of C*-algebras
   `0 -> C_0(U) -> C(X) -> C(Z) -> 0`.

2. **The two rows.** By item 3 of
   `amenable-kernel-bc-transfer-and-ktop-half-exactness` (Chabert--Echterhoff,
   Kasparov--Skandalis), `A ↦ K^top_*(G; A)` is half exact and assembly is
   natural in `A`. So the sequence induces a commuting ladder, in each degree `j`,

   ```text
   K^top_j(G; C_0(U)) --i*--> K^top_j(G; C(X)) --res*--> K^top_j(G; C(Z))
        | mu_(G,C_0(U))            | mu_(G,C(X))              | mu_(G,C(Z))
        v                          v                          v
   K_j(C_0(U) ⋊_r G) --i*--> K_j(C(X) ⋊_r G) --q*--> K_j(C(Z) ⋊_r G)
   ```

   The top row is exact at the middle term (half-exactness). The squares commute
   (naturality).

3. **All verticals are isomorphisms.** `G` satisfies Baum--Connes with
   coefficients, so `mu_(G,A)` is an isomorphism for every separable `G`-C*-algebra
   `A`. Here `C_0(U)`, `C(X)`, `C(Z)` are separable, since `V` is countable makes
   `X = V^` a compact metrizable group. Hence all three vertical maps are
   isomorphisms.

4. **Exactness transports.** A commuting ladder whose vertical maps are
   isomorphisms and whose top row is exact at the middle has its bottom row exact
   at the middle: `ker q_* = mu_(G,C(X))(ker res_*) = mu_(G,C(X))(im i*) =
   im i*` on the bottom. So the crossed-product K-theory sequence is exact at
   `K_j(C(X) ⋊_r G)`, for both `j`. This is the Theorem.

5. **Contrapositive.** If the bottom middle is not exact in degree `j`, some
   vertical fails to be an isomorphism. `mu_(G,C_0(U))` plays no role in step 4
   beyond the diagram (the chase uses only surjectivity of `mu_(G,C(X))` and
   injectivity of `mu_(G,C(Z))`), so the failure is: `mu_(G,C(X))` not surjective
   or `mu_(G,C(Z))` not injective in degree `j`. Either is a coefficient failure
   of Baum--Connes for `G`. (This is the same step 3--4 as the sibling proof route,
   read in the direction that constrains the base group rather than the tower.)

6. **Non-vacuousness.** By `higson-kasparov-haagerup-satisfies-bcc`, a-T-menable
   groups satisfy BCC and some are non-exact. So step 3 applies to genuinely
   non-exact groups, and the Theorem is not an exact-group statement in disguise.
