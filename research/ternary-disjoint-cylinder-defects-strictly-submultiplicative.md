---
rg: 2
id: ternary-disjoint-cylinder-defects-strictly-submultiplicative
kind: claim
title: In anti-central characteristic-three rank models of the ternary Leavitt unit group, two-root defects on disjoint cylinders multiply strictly below independence
distinct_from:
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the binary statement over F_2 for fixed-point-free models; this is the ternary anti-central statement over F_3, where anti-central models are automatically fixed-point-free and the regular defect is 5/9 rather than 3/8.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the abstract No branch of the ternary gate; this is a strict deficit in products of commuting cylinder defects, which with a characteristic-three defect gap and near-minimal multiplicativity would give the matricial No branch.
  anti-central-sofic-data-cannot-force-defect-submultiplicativity: that is the firewall, realizing theta = 1 on sofic and locally finite HNN data; this is the open strict deficit.
artifacts:
  - research/artifacts/char-three-anti-central-defect-firewall-2026-09-12.md
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

**OPEN.** There is `theta < 1` with the following property. Let `sigma` be a nontrivial anti-central
characteristic-three rank model of `G = L_(F_3)(1,2)^x`, into a rank ultraproduct over fields of characteristic
three, and let `A`, `B` be disjoint proper cylinders. Then

```text
rk(D_A D_B)  <=  theta · rk(D_A) · rk(D_B) ,        D_A = N^A_23 N^A_12 .
```

**Abstract form.** The same inequality for anti-central models in abstract `F_3`-rank algebras.

**Payoff.**
- **Matricial.** Together with characteristic-three ports of the defect gap and of near-minimal multiplicativity
  (`two-root-defect-descent-gap-2026-09-12.md`, Sections 2 and 4; lane `w5-c3-descent`), it excludes
  near-minimal anti-central models, hence every nontrivial anti-central model. Every nontrivial
  characteristic-three model compresses to an anti-central one (`ternary-leavitt-rank-models-move-z-iff-nontrivial`),
  so all are trivial, which is the matricial No branch of the ternary gate.
- **Abstract.** With abstract ports of those two results it would give
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`, and with (U1) the counterexample chain.
- **What the ports must cover.** The descent artifact uses regular-ring facts (images, annihilators, the modular
  lattice of principal right ideals: its Fact 1.1(a),(b),(d)) and compactness over finite matrix stages (Lemma 2.3).
  Both are matricial or regular-ring steps. No route is landed yet, because those ports have no nodes on main.

**Simplification in characteristic three.** Anti-central models have no fixed vectors: `sigma(g)b = b` for all `g`
gives `b = -b`, so `b = 0`. The fixed-point-free quotient step is automatic.

## Attempts

- **Finite-subgroup, sofic and HNN data give `theta = 1` (w5-c3-submult, 2026-09-12;
  `anti-central-sofic-data-cannot-force-defect-submultiplicativity`).**
  * **Profile.** The anti-central regular profile has `rk(N_12) = 2/3`, `rk(D_A) = 5/9` and exactly
    multiplicative disjoint defects, `(5/9)^k`. The count is the kernel of `(y-1)(x-1)` on `F_3[UT_3(F_3)]`.
  * **Realized on.** Genuine anti-central models of every sofic subgroup containing `z`, and of every locally
    finite HNN datum.
  * **Covered.** The anti-central sign, the Haar law, the torus normal form (`rk(N^2) = 1/3` there), the four odd
    weight spaces, reflections inverting roots, halving sheets and single conjugations by units.
- **Characteristic-three inputs are finite-subgroup data.** Every input the launch listed as possibly breaking
  `theta = 1` (anti-central sign, Haar law, `A^3 = 0` with `N = A - A^2`, weight spaces of rank `1/4`) holds in
  that profile. None of them gives a deficit.
- **Where a proof must live.** Identities multiplying conjugating units with defects inside a nonsofic subgroup
  containing `z` and the frames, or a global input: corner locality through the defect gap, or compactness.
  - The char-2 commutant constraint (`near-minimal-defects-are-rank-independent-of-cylinder-commutants`) should
    port and would pin products with everything commuting with `sigma(iota_A(G))`.
  - `z` lies in every such commutant, so the anti-central sign cannot enter a deficit as a factor.
