---
rg: 2
id: simple-group-width-over-congruence-targets
kind: claim
title: A finitely presented simple group has bounded relator width over all congruence groups SL_n(R) of finite chain rings iff it is not linear sofic over finite fields
distinct_from:
  simple-group-psl-width-is-finite-field-linear-soficity: that is the residue-field case R = F_q; this lets the ring be any finite chain ring, so the p-group congruence kernel of unbounded class under an unbounded top must be covered.
  relator-width-over-nilpotent-by-locally-finite-groups: that covers congruence towers over one fixed residue group SL_n(q); this lets n, q and the length of the ring grow together.
  relator-width-over-transitive-abelian-extensions: that absorbs one abelian layer on which the group is transitive; this absorbs every adjoint congruence layer, where classes are graded by rank and transitivity fails.
---

**ESTABLISHED (unreviewed, 2026-09-13, lane `ex2-weak-sofic-affine-targets`).**

A **finite chain ring** is a finite local ring with principal maximal ideal: `F_q[t]/(t^k)`, `Z/p^k`,
`O_K/p^k`. Let `G = <X | R>` be an infinite finitely presented simple group, with `w_Q(a)` as in
`simple-group-relator-width-in-finite-simple-targets`, and "linear sofic over finite fields" as defined
on `simple-group-psl-width-is-finite-field-linear-soficity`.

**Theorem B.**
1. **Bounded rank, no hypothesis.** For every `n_0` there is `K(G, n_0)` with `w_Q(a) <= K(G, n_0)` for
   every `Q = SL_n(R)/Z_0` with `2 <= n <= n_0`, every finite chain ring `R`, every central `Z_0` and every
   `a in Q^X`. The residue field and the length of `R` are unrestricted.
2. **Dichotomy.** The following are equivalent:
   - (i) `G` is not linear sofic over finite fields;
   - (ii) there is `K(G)` with `w_Q(a) <= K(G)` for all `Q = SL_n(R)/Z_0`, all `n >= 2`, all finite chain
     rings `R` and all central `Z_0`;
   - (iii) `G` has no sequence of weak models into these groups with bi-invariant lengths.
3. **Affine congruence groups.** Under (i), the width is also bounded over `R^n x| SL_n(R)`.

**In words.** Deep congruence structure under a classical top adds nothing: the weak models of a finitely
presented simple group into `SL_n(Z/p^k)` or `SL_n(F_q[t]/t^k)`, with `n`, `q` and `k` all unbounded, exist
iff it is linear sofic over finite fields.

**Mechanism.**
- **Kernel by two Singer tori.** Two Singer elements of `SL_n(q)` whose centralizers meet in the scalars
  make the linearized commutator map onto each layer `sl_n(F_q)`. Successive approximation writes every
  element of the congruence kernel as `[g_1, b_1][g_2, b_2]`, for any lifts `g_i`, uniformly in the length
  of `R`. So a normal subset whose residues cover `PSL_n(q)` in `k_0` steps covers `SL_n(R)` in `5 k_0`
  steps, up to Teichmueller scalars.
- **Residues proportional or bounded rank.** Liebeck--Shalev in `PSL_n(q)`, then the kernel step.
- **Residues scalar.** The tuple lies in a nilpotent group, where
  `perfect-group-relator-width-over-nilpotent-groups` applies.
- **Residues near-scalar.** The block of the kernel parts away from the moved subspace is an
  approximate homomorphism into a `p`-group, with defect of rank `<= d_0` per multiplication.
  - The nilpotent template with block-diagonal conjugators matches it at every level at once.
  - The displacement of `simple-group-classical-width-finite-field-linear-soficity` cancels the relator's
    big block up to rank `2 d_0`.
  - A free-summand localization then puts remainders and seed in `SL_(O(P))(R)`, where the kernel step
    applies.

**Model test.**
- *Trivial model.* A sofic group fails (i), and its width is unbounded already over `R = F_q`.
- *Real object.* No finitely presented simple group is known to satisfy (i). So (i) => (ii) is a
  reduction. (iii) => (i), item 1, and the bound over congruence towers in fixed rank are unconditional.
- *Where each hypothesis is used.* Item 1 uses none. The near-scalar and proportional cases for unbounded
  `n` use the uniform collapse constant of (i).

**For the rigidity claim.** A counterexample to `fg-simple-weakly-sofic-groups-are-sofic` gets no room from
congruence groups over classical special linear tops unless it is linear sofic over finite fields. The
same holds for the affine groups of `relator-width-over-transitive-abelian-extensions`.

**Not covered.**
- Isometry groups `Sp`, `SU`, `Omega` over chain rings. They need a Singer-type pair in the isometry Lie
  algebra and a lift of the displacement. Not written.
- Non-chain local rings such as `F_q[x, y]/(x, y)^2`. The free-summand localization uses Smith normal form.
- `p`-groups under `SL_n(q)` with other module layers, for example many copies of the natural module or
  `Lambda^2`.
- `GL_n(R)` and tops with a large abelian quotient.

Derivation: `simple-group-width-over-congruence-targets-proof`. Credit: elementary, beyond the
Liebeck--Shalev import. Bounded graph check: no node on congruence targets with unbounded rank. No
literature search on Singer pairs with trivial common centralizer; the fact is elementary.
