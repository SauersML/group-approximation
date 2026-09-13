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
- **Payoff check (w5-c3-descent; `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md`).**
  - **The gap ports, abstractly.** `ternary-anti-central-two-root-defect-has-a-uniform-gap`: the minimum `c_3`
    is attained in both scopes.
  - **Near-minimal multiplicativity does not port**, in either scope (artifact Remark 3.3 and Section 4).
    * Its lower bound `f(k+1) >= c_* f(k)` needs range corners, globality and kernel corners.
    * The ternary lower bound that does hold is sector-limited: `f(k+1) >= c_3 N(Q_B P_k)`
      (`ternary-cylinder-defect-products-descend-in-sign-sectors`).
    * So the Payoff paragraph above has no available port, and this claim alone does not close.
  - **The form that closes** is `ternary-anti-central-disjoint-defects-have-a-strict-deficit`: disjoint products
    are nonzero, and compressing along `Q_B D_A` lowers the defect by `theta < 1`. It has a landed route to
    `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.
- **Multi-letter firewalls in characteristic three (w7-sub-multiletter, 2026-09-12).** Artifact
  `research/artifacts/multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md`; held OPEN until `w4-vf-gate`
  re-derives it.
  * **Lexicographic Borel group** (artifact Section 3).
    - The artifact's Lemmas 3.1–3.4 use only the monomial calculus. So over `F_3` the lexicographically decreasing
      unipotents `U_<` form a locally finite 3-group containing `iota_A(UT_3(R))` at every cylinder, and Thompson's
      `F` normalizes it.
    - `-1` lies outside `U_< ⋊ P` for `P <= F`. So for amenable `P`, `<-1> x (U_< ⋊ P)` is amenable data for
      `anti-central-sofic-data-cannot-force-defect-submultiplicativity`. This covers the depth-changing letter `x_0`
      with the frames at `0` and `1`.
  * **Cylinder swaps** (artifact Section 2).
    - Permuted tensor powers model copies of `G` at incomparable `A` and `B`, together with the swap between them,
      with exactly multiplicative defects.
    - When `[A] cup [B]` is proper, `z` is not in that group and can be sent to `-1`. This matches the
      independent-factor remark on `ternary-anti-central-disjoint-defects-have-a-strict-deficit`.
    - When `[A] cup [B] = X`, `z = iota_A(-1) iota_B(-1)` goes to `+1`, so that case gives no anti-central model.
