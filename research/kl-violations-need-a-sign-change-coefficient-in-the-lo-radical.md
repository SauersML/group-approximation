---
rg: 2
id: kl-violations-need-a-sign-change-coefficient-in-the-lo-radical
kind: claim
title: An equation that fails to inject its group needs a sign-change coefficient in the orderable radical, or a radical image that is a proper power
distinct_from:
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that works at exponent sum ±1 only and needs every coefficient to have infinite order; this works at every exponent sum and puts no condition on the same-sign coefficients, which may be torsion, but needs the sign-change coefficients to survive in an orderable quotient.
  kl-sign-index-two-infinite-order-loops-inject: that needs exactly two sign changes and infinite order at both sign-change coefficients; this allows any number of sign changes and every exponent sum, but asks for survival in an orderable quotient instead of infinite order.
  nonsingular-adjunction-preserves-approximation-radicals: that confines the kernel to the matrix and hyperlinear radicals; this confines the coefficients responsible for a failure to the orderable radical, which is not an approximation radical and is nontrivial in every group with torsion.
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that needs the same-sign labels to be free and imposes only non-absorption on the sign-change coefficients, which may be torsion; this needs the sign-change coefficients to survive in an orderable quotient and imposes nothing on the same-sign labels.
  orderable-quotient-stackings-inject-the-kernel: that needs every coefficient to survive in the orderable quotient; this removes the condition at the same-sign coefficients by a change of variable.
artifacts:
  - experiments/kl-orderable-radical-screen-2026-09-17/calibrate.g
  - experiments/kl-orderable-radical-screen-2026-09-17/calibrate.out
---

**Status: proposed ESTABLISHED** by `kl-lo-radical-sign-change-screen-proof`.
It uses `orderable-quotient-stackings-inject-the-kernel` and is not
independently reviewed.

**Setting.** Let `G` be any group. Let `w ∈ G * <t>` be cyclically reduced and
not in `G`. Write it with single letters,

    w = c_1 t^(e_1) c_2 t^(e_2) ... c_N t^(e_N),     e_j ∈ {+1, -1},

where the coefficients `c_j ∈ G` may be `1`. Indices are cyclic.
- Position `j` is a **sign change** if `e_(j-1) ≠ e_j`. There `c_j ≠ 1`, by
  cyclic reducedness.
- Position `j` is a **same-sign position** otherwise.

Let `R(G)` be the orderable radical (the smallest normal subgroup with
right-orderable quotient), `Q = G/R(G)`, and `π: G * <t> -> Q * <t>` the induced
map.

**Theorem.** Suppose that
- (a) every sign-change coefficient `c_j` lies outside `R(G)`;
- (b) `Q ≠ 1`, which follows from (a) whenever `w` has a sign change; and
- (c) `π(w)` is not a proper power in `Q * <t>`.

Then `G -> (G * <t>)/<<w>>` is injective. This holds at every exponent sum.

**Contrapositive (the screen).** If `(G, w)` violates
`kervaire-laudenbach-nonsingular-conjecture`, or the same injectivity at exponent
sum `0`, then one of the following holds:
1. some sign-change coefficient lies in `R(G)`;
2. `w` has no sign change and `G` has no nontrivial right-orderable quotient;
3. the image of `w` over the orderable quotient is a proper power.

By `kl-failure-localizes-to-the-coefficient-subgroup`, the violation already
occurs over the coefficient subgroup `A`. Since `R(A) ⊆ R(G) ∩ A`, applying the
screen to `A` gives a sharper conclusion: some sign-change coefficient lies in
`R(A)` (or case 2 or 3 holds for `A`).

**What it says about counterexamples.** A counterexample needs a sign-change
coefficient that dies in every right-orderable quotient of the finitely
generated coefficient group. Torsion elements do this, and so do elements of
perfect subgroups with no orderable quotient. The same-sign coefficients are
completely unconstrained: they may be torsion, `1`, or anything else. Levin's
theorem already handles words with no sign change, so case 2 is not new
information.

**What it newly reaches.** Words with any number of sign changes, at any
exponent sum, over groups with arbitrary torsion, provided the sign-change
coefficients survive in some right-orderable quotient. Example: `G = K × Z`
with `K` arbitrary (a free Burnside group, say), every sign-change coefficient
with nonzero `Z`-coordinate, and the `Z`-image of the word not a proper power.
Klyachko needs every block coefficient of infinite order and exponent sum ±1.
Stallings and Clifford–Goldstein need exactly two sign changes. The
hyperlinear theorems need `K` hyperlinear.

**Calibration.**
- **Negative controls, where the screen allows a kill.**
  - Over `Z/2 * Z/3`, `w = a t b t^(-1)` kills `a`. Both coefficients are
    sign-change coefficients in `R(G) = G`, so case 1 holds.
  - Over `<s> × <c | c^2>`, `w = c t s t^(-1)` gives `t s t^(-1) = c^(-1)`, so
    `s^2 = 1`. The sign-change coefficient `c` is torsion, so case 1 holds.
- **Positive controls.** Over `G = <s> × <c | c^2>` the theorem predicts
  injectivity for:
  - `s t c t s t^(-1)`;
  - `sc t c t s t^(-2)` (exponent sum 0);
  - `sc t s^(-1) t^(-1)`;
  - `s t c t c t s t^(-1)`.

  In each case the torsion coefficient `c` sits at a same-sign position, or
  (in the third word) inside a sign-change coefficient that survives in `Z`.
  `experiments/kl-orderable-radical-screen-2026-09-17/calibrate.g` certifies,
  by permutation representations of index at most 8, that `c`, `s`, `sc`,
  `s^2 c` and `s^2` survive in all four quotients (`calibrate.out`). This is a
  consistency check, not a proof of injectivity.
