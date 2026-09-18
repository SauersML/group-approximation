---
rg: 2
id: invariant-background-certificates-miss-difference-units-proof
kind: route
title: Conjugates of a wandering idempotent give a one-column factorization, and the invariant background cancels the difference unit off the support
target: invariant-background-certificates-miss-difference-units
requires:
  - coset-field-rank-condition-is-lamp-factorization
---

## (A) Compression

**One piece.** Let `y = Q y` with `Q` wandering. Fix `d` and choose `g_1, ..., g_d` with
`Q u_(g_j^(-1) g_l) Q = 0` for `j != l`. Put `a_j = Q u_(g_j)^(-1)` and `b_l = u_(g_l) y`. Then

    a_j b_l = Q u_(g_j^(-1) g_l) y = Q u_(g_j^(-1) g_l) Q y,

which is `0` for `j != l` and `Q Q y = y` for `j = l`. So the column `X = (a_j)` and the row `Y = (b_l)` give
`XY = y I_d` through `M^1`.

**Several pieces.** If `y = sum_(i=1)^m y_i` with `y_i = Q_i y_i`, take `X_i, Y_i` for each piece and put
`X = [X_1 ... X_m]` (`d x m`) and `Y = [Y_1; ...; Y_m]` (`m x d`). Then `XY = sum_i X_i Y_i = y I_d`.

**Rank zero.** For a normalized Sylvester matrix rank function, `d rk(y) = rk(y I_d) = rk(XY) <= rk(X) <= m`
for every `d`, so `rk(y) = 0`.

## Disjoint translates (Neumann's lemma, with proof)

**Covering lemma** (B. H. Neumann, J. London Math. Soc. 29 (1954), 236-248). A group is not a finite union of
cosets `g_i K_i` of subgroups `K_i` that all have infinite index.

*Proof.* Induct on the number of distinct subgroups among the `K_i`. With one subgroup `K`, finitely many cosets
of `K` would cover `G`, so `[G:K]` would be finite. Otherwise fix one of them, `K`. Since `[G:K]` is infinite, some
coset `xK` is none of the listed `K`-cosets. Distinct `K`-cosets are disjoint, so `xK` lies in the union of the
listed cosets of the other subgroups. Translating, every coset `yK = (y x^(-1)) xK` lies in finitely many cosets of
those subgroups. Replacing each listed `K`-coset in this way covers `G` by cosets of fewer distinct subgroups, all
still of infinite index. This contradicts the induction hypothesis.

**Consequence.** Let every `G`-orbit on `H` be infinite and `F, F'` be finite. The set `{g : gF meets F'}` is the
union over `a in F`, `b in F'` with `b in Ga` of the cosets `h_(a,b) Stab(a)`, where `h_(a,b) a = b`. Each
`Stab(a)` has infinite index, since the orbit of `a` is infinite. By the covering lemma some `g` has
`gF ∩ F' = ∅`. Inductively, for every `n` there are `g_1, ..., g_n` whose translates `g_j F` are pairwise
disjoint: choose `g_(n+1)` with `g_(n+1) F` disjoint from `g_1 F ∪ ... ∪ g_n F`.

## (B) Support form

Fix `c != c'`, put `F = {c, c'}`, and write `h.z = u_h z u_h^(-1)`, an automorphism of the commutative ring `D`.
For each layer `i` let `P_i = P_c^(i) + P_(c')^(i) - P_c^(i) P_(c')^(i)`, the join of two commuting idempotents,
so that `1 - P_i = (1 - P_c^(i))(1 - P_(c')^(i))`. Put `Z = prod_i (1 - P_i)`.

**The background cancels.** Since `Z` contains the factor `prod_i (1 - P_c^(i))` and `D` is commutative,
`phi(x_c) Z = lambda Z`, and likewise `phi(x_c') Z = lambda Z`. So `y = phi(x_c - x_c')` has `yZ = 0`, and hence
`y = y(1 - Z) = (1 - Z) y`.

**Splitting the support.** `1 - Z = sum_(i=1)^m E_i` with `E_i = P_i prod_(j<i) (1 - P_j)`. These are pairwise
orthogonal idempotents of `D`, and `E_i <= P_i`, meaning `E_i = E_i P_i`. Put `y_i = E_i y`. Then
`y = sum_i y_i` and `E_i y_i = y_i`.

**Each E_i wanders.** For `h in G`, equivariance gives `h.P_i = P_(hc)^(i) ∨ P_(hc')^(i)`. If `hF ∩ F = ∅`,
every product `P_a^(i) P_b^(i)` with `a in F` and `b in hF` is `0`, because `a != b`. Expanding the joins then gives
`P_i (h.P_i) = 0`, and so `E_i (h.E_i) = E_i P_i (h.P_i)(h.E_i) = 0`. Now `E_i u_h E_i = E_i (h.E_i) u_h = 0`.
Choose `g_1, ..., g_n` with the `g_j F` pairwise disjoint, as in the previous section. Then
`h = g_j^(-1) g_l` satisfies `hF ∩ F = ∅` for `j != l`, so `E_i u_(g_j^(-1) g_l) E_i = 0`.

Part (A) applies to `y = sum_i y_i`. So `phi((x_c - x_c') I_d) = y I_d` factors through `M^m` for every `d`, and
`rk(y) = 0` for every normalized Sylvester matrix rank function on `M`. By
`coset-field-rank-condition-is-lamp-factorization`, a certificate refutes `A_0 B_0 = w I_d` with inner size `r` only
by showing that `phi(w) I_d` does not factor through `M^r`. For `w = x_c - x_c'` and `r >= m` it does factor, so
`phi` cannot refute it.

## (C) Nilpotent images

In `k[(Z/p^n) wr_H G]` with `char k = p`, the images of `x_c` and `x_c'` commute and satisfy `x^(p^n) = 1`.
Frobenius gives `(x_c - x_c')^(p^n) = x_c^(p^n) - x_c'^(p^n) = 0`. In `T / J^N`, `x_c - x_c'` equals
`(x_c - 1) - (x_c' - 1)`, which lies in `J`, so its `N`-th power is `0`. If `rk(y) = 1` for a normalized
Sylvester matrix rank function, the Sylvester inequality `rk(ab) >= rk(a) + rk(b) - 1` gives `rk(y^j) = 1` for
every `j`, which contradicts `rk(0) = 0`.

## Coverage and calibration

The formula `Phi_r(x_c) = tensor_i (1 + (t - 1) e_c^(i))` comes from `diagonal-tensor-orbit-corner-induction-proof`.
There `v_n` is `[n(x)]` at the site `x` and `1` at infinity. In each factor, `(1 + (t - 1) e_c)(1 - e_c) = 1 - e_c`,
so the support-form identity holds with `lambda = 1`. Distinct site units `e_a` and `e_b` of the direct sum are
orthogonal, and `G` permutes them.

For `G = Z` acting regularly on `Z`, `K semidirect Z` is a skew Laurent extension of a field. It is an Ore domain,
so it embeds in a division ring and has the rank condition. Its orbits are infinite, so (B) applies unchanged.
