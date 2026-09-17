---
rg: 2
id: char-zero-kun-thom-double-reduces-nonsofic-atiyah-to-edge
kind: claim
title: A torsion-free nonsofic double of Strong Atiyah groups over Kazhdan edges decides between a nonsofic Strong Atiyah group and a counterexample
distinct_from:
  nonsofic-group-satisfying-strong-atiyah: that is the open existence question; this produces one explicit torsion-free nonsofic group whose vertex and edge groups satisfy Strong Atiyah, and proves that the edge permanence implies the existence question.
  kt-pair-group-double-is-nonsofic: that records Kun--Thom's Theorem A conclusion for doubles over the positive-characteristic Theorem E pair, which has torsion; this verifies the Theorem A hypotheses for the characteristic-zero pair and passes to a torsion-free finite-index subgroup with Strong Atiyah vertex groups.
  strong-atiyah-kazhdan-edge-amalgam-permanence: that is the general permanence for one amalgam over an infinite (T) edge; this is one explicit nonsofic instance of iterated such amalgams, where both the permanence and its failure settle a named open node.
  double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree: that reduces a multiple ascending HNN extension, not known to be nonsofic, to the same permanence; this does it for a group proved nonsofic.
artifacts:
  - experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py
---

**ESTABLISHED** by [[char-zero-kun-thom-double-reduction-proof]]. It rests on
Kun--Thom Theorem A (arXiv:2608.06222 v3, unrefereed) and on
[[kun-thom-actor-strong-atiyah-via-formal-torus]].

**Setting.** Let `r, d >= 3`, let `p >= 3` be prime, and let
`R = Z[x_1^(+-1),...,x_d^(+-1)]`. Take `G_0 = EL_r(R) semidirect SL_d(Z)` and
`H = K semidirect Gamma_d(p)` as in
[[char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup]]. Put

```text
Gamma = EL_r( Z[x_1,...,x_d] ) <= G_0,     D = G_0 *_Gamma G_0,
f : D -> G_0  the fold (identity on both factors),     D_H = f^-1(H).
```

## Statement

1. **The Kun--Thom hypotheses hold in characteristic zero.** `Gamma` is
   infranormal and not normal in `G_0`, and both groups have property (T). So
   `D` is not sofic, by Kun--Thom Theorem A as recorded in
   [[kt-pair-group-double-is-nonsofic]].
2. **The torsion-free double.** `D_H` has finite index in `D`, so it is not
   sofic. It is torsion-free, and `D_H = F semidirect H`, where `F = ker f` is
   free.
3. **Its graph of groups.** `D_H` is the fundamental group of a finite graph of
   groups:
   - two vertices, each carrying a copy of `H`;
   - `|SL_d(F_p)|` edges joining them, with edge groups `H cap g Gamma g^-1`;
     each is an infinite property (T) group.

   Every vertex and edge group satisfies Strong Atiyah over `C`, by
   [[kun-thom-actor-strong-atiyah-via-formal-torus]].
4. **Dichotomy.**
   - If `D_H` satisfies Strong Atiyah over `C`, then
     `nonsofic-group-satisfying-strong-atiyah` holds, witnessed by `D_H`.
   - If it does not, `strong-atiyah-torsion-free` is false, and a witness matrix
     over `C[D_H]` is not supported in any vertex group.
5. **Reduction.** `strong-atiyah-kazhdan-edge-amalgam-permanence` over `C`
   implies that `D_H` satisfies Strong Atiyah over `C`, and therefore implies
   `nonsofic-group-satisfying-strong-atiyah`. Only the amalgams of the tree of
   groups of `ker( D_H -> F_(m-1) )` are needed, where `m = |SL_d(F_p)|`. These
   are finite trees with vertex groups conjugates of `H` and edge groups
   conjugates of `H cap g Gamma g^-1`.

Only the direction "permanence implies existence" is proved. The converse is
not claimed.

## What it changes

* **Before.** The Attempts of `nonsofic-group-satisfying-strong-atiyah`
  recorded "No torsion-free rigid pair with `G` satisfying Strong Atiyah is
  recorded". They also recorded that Theorems A and E were unchecked in
  characteristic zero.
* **Now.** One explicit torsion-free, nonsofic group with exact
  multiplication, built from Strong Atiyah pieces, stands between the two open
  nodes. Settling Strong Atiyah for this single group settles one of them.
* **Where approximation dies.** `D_H` is nonsofic, so no residual chain of
  sofic quotients exists. Soficity passes to residually sofic groups. The
  `u`-adic chain of the vertex groups does not extend to `D_H` with sofic
  quotients.
* **Where the known permanence dies.**
  - The locally indicable extension theorem reaches the free quotient `F_(m-1)`,
    but its kernel is a tree of Kazhdan-edge amalgams.
  - The other extension, `F semidirect H`, has a Kazhdan quotient that is not
    locally indicable.
  - Sanchez-Peralta's graph-of-groups permanence needs finite edge groups.

## Model test

* **Trivial model.** At `p = 2` the vertex group has torsion, `-I in K`, and
  the construction is not torsion-free. So item 2 genuinely uses `p >= 3`.
* **Calibration of the fold.**
  - The kernel of a fold `A *_C A -> A` meets each vertex group trivially.
  - So it acts freely on the Bass--Serre tree, and it is free.
  - This reproduces the free kernel of the classical double `Z *_(2Z) Z -> Z`.
* **Nonsoficity calibration.** The positive-characteristic pair has torsion. By
  `kun-thom-actors-have-no-torsion-free-finite-index-subgroups` it has no
  torsion-free finite-index subgroup. That is why the characteristic-zero pair
  is needed here.
* **Script.** Check 7 of
  `experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py` verifies:
  - nonnegative substitutions compress `Z[x]`;
  - `I - E_12` sends `x_2` to `x_1^-1 x_2`, which gives non-normality.

## Attempts

- **Extend the formal-torus chain to the double (2026-09-17, sw-066).** *Dies*
  at the first truncation, for an exact reason.
  - Let `I = (x_1 - 1, ..., x_d - 1)` and `L_n = ker( EL_r(R) -> GL_r(R/I^n) )`.
    It is normal in `G_0`, because every `alpha_A` preserves `I`, and the `L_n`
    intersect trivially (Krull).
  - In `R/I^n` every `x_i = 1 + u_i` has the polynomial inverse
    `sum_(k<n) (1 - x_i)^k`, so `P = Z[x]` maps onto `R/I^n`. Hence
    `EL_r(P)` and `EL_r(R)` have the same image, and `Gamma L_n = EL_r(R)`.
  - Killing `L_n` in both factors gives the pushout
    `D_n = G_0/L_n *_(Nbar_n) G_0/L_n` with `Nbar_n = EL_r(R)/L_n` **normal** in
    both factors. So `D_n = Nbar_n semidirect (SL_d(Z) * SL_d(Z))`, acting through
    the fold, and `(fold, quotient by Nbar_n)` embeds `D_n` in
    `(G_0/L_n) x (SL_d(Z) * SL_d(Z))`. That product is residually finite:
    `G_0/L_n` acts faithfully and `Z`-linearly on `(Z[u]/(u)^n)^r` for `n >= 2`.
  - Therefore `ker( D -> lim D_n ) = ker( D -> G_0 x (SL_d(Z) * SL_d(Z)) )`. It
    contains `g^(1) (g^(2))^-1` for every `g in EL_r(R) - Gamma`, for example
    `g = e_12(x_1^-1)`, so it is nontrivial. This does not use nonsoficity.
  - Infranormality without normality, the Kun--Thom input, is invisible at every
    finite `u`-adic level. Any rank argument for `D_H` must work in the `u`-adic
    limit (the completed vertex groups `W_(r,d,p)`), not along truncations.
