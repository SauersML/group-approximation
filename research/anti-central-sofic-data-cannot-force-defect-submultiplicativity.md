---
rg: 2
id: anti-central-sofic-data-cannot-force-defect-submultiplicativity
kind: claim
title: Anti-central regular ranks give ternary cylinder defects of rank five ninths that multiply exactly, realized on every sofic subgroup and every locally finite HNN datum
distinct_from:
  finite-subgroup-data-cannot-force-defect-submultiplicativity: that is the characteristic-two regular assignment with defect 3/8 and no central involution; this is the anti-central assignment over F_3, twisted by eps_-, with defect 5/9, realized by genuine models of sofic subgroups and HNN data.
  locally-finite-hnn-data-allow-independent-cylinder-defects: that is the characteristic-two HNN model over F_2; this is the anti-central characteristic-three model over an arbitrary locally finite base containing z.
  sofic-subgroups-carry-rank-models-violating-two-root-identity: that turns sofic approximations into F_2 models free on one D_8; this compresses F_3 permutation models to the -1 eigenspace of z and computes the whole cylinder-defect profile.
  level-unit-hnn-extensions-have-anti-central-rank-models: that builds the twisted regular tower on the level unit group and its HNN extensions; this generalizes the base to every locally finite subgroup containing z, adds sofic subgroups, and computes rho(D_A) = 5/9 with exact multiplicativity.
  ternary-disjoint-cylinder-defects-strictly-submultiplicative: that is the open strict deficit in characteristic three; this shows which inputs cannot prove it.
artifacts:
  - research/artifacts/char-three-anti-central-defect-firewall-2026-09-12.md
---

**ESTABLISHED** (route `anti-central-sofic-data-defect-firewall-proof`; artifact Sections 1–2; independent
re-derivation requested from `w4-vf-gate`).

**Setting.** `G = L_(F_3)(1,2)^x`, `z = -1`, `eps_- = (1 - [z])/2`, the code `(0, 10, 11)`,
`D_A = N^A_23 N^A_12` with `N^A_ab = sigma(iota_A(x_ab(1))) - 1`.

**Statement.**
1. **Profile.** For `alpha` supported in a finite subgroup `K` containing `z`, put
   `rk^-(alpha) = dim(alpha F_3[K] eps_-)/(|K|/2)`. It is well defined, invariant under conjugation by every unit
   of `G`, and has `rk^-(1 - [z]) = 1`.
2. **Values.** `rk^-(N^A_12) = 2/3`, `rk^-(D_A) = 5/9`, and for pairwise disjoint proper cylinders
   `rk^-(D_(A_1) ... D_(A_k)) = (5/9)^k`. The computation is the kernel count in `F_3[UT_3(F_3)]`.
3. **Locally finite HNN data.** For a countable locally finite `L' <= G` containing `z` and countable `U ⊆ G`, the
   HNN group with letters `t_u` acting on `L' cap u^-1 L' u` has an anti-central rank model over `F_3` realizing
   `rk^-` on finite subgroups of `L'`, with no fixed vectors.
4. **Sofic subgroups.** Every sofic `S <= G` containing `z` has an anti-central rank model over `F_3` realizing
   `rk^-` on its finite subgroups.

**Consequence.** No `theta < 1` in `ternary-disjoint-cylinder-defects-strictly-submultiplicative` follows only
from identities inside one sofic subgroup containing `z`, identities of a locally finite subgroup plus single
conjugations, the anti-central sign, the Haar law, the torus normal form, weight-space ranks, and rank calculus.
The models are abstract rank algebra models, so this holds for Sylvester rank functions too. A proof must use
identities that multiply conjugating units with defects inside a nonsofic subgroup containing `z` and the frames,
or a global input.

**Scope.** Every step is a finite-dimensional computation or an ultraproduct of matrices, used only to build
counter-models. Nothing here is a triviality statement, so no abstract-scope audit is needed for it to apply to
abstract rank functions.

## Attempts

- Established, not open. Proof: free-module consistency, the Heisenberg kernel count, tensor factorization over
  disjoint cylinders, the moving-index intertwiners of the HNN artifact over a general locally finite base, and
  compression of sofic permutation models to the `-1` eigenspace of `z`.
