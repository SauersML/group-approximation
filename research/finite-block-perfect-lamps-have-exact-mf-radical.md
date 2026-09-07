---
rg: 2
id: finite-block-perfect-lamps-have-exact-mf-radical
kind: claim
title: Finite perfect blocks give finitely presented sofic groups with an exact residually finite MF radical
distinct_from:
  wreath-compression-mf-radical: That imposes commutation across all sites and produces groups that are not finitely presented; this only imposes commutation inside finite blocks and proves finite presentability.
  literal-mf-radical-is-unsquared-defect: That computes a defect subgroup in the Clifford block amalgam; here the entire ordinary free-product lamp kernel is perfect, residually finite, and exactly the MF and finite residual.
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

Let Gamma be finitely presented with property (T), let alpha be an injective
endomorphism of index m>1, and assume its ascending HNN extension V is
residually finite. Put Gamma+=t^-1 Gamma t, X=V/Gamma, Y=V/Gamma+, and
let p:X->Y be the coset map. For every nontrivial finite perfect group K,

    B_K = *_(y in Y) product_(x in p^-1(y)) K_x,
    G_K = B_K semidirect V

is finitely presented, sofic, and not MF, and

    Rad_MF(G_K) = Res_fin(G_K) = B_K,
    G_K/Rad_MF(G_K) ~= V.

The kernel B_K is itself perfect and residually finite. Also
G_K=J_K semidirect Z with J_K locally residually finite, and the canonical
maximal trace of G_K is amenable and not quasidiagonal. For K nonabelian
simple, any nonidentity coordinate element normally generates B_K.

With Gamma=Z^3 semidirect SL_3(Z), alpha doubling the translations, and
K=A_5, the example is centerless and its radical is a free product of
countably many copies of (A_5)^8. The complete written proof is in
Sections 3--4 of the artifact; no new Lean endpoint is claimed.
