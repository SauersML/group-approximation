---
rg: 2
id: sp4-quasirep-windings-budget-and-saturation
kind: claim
title: Maslov windings of Sp4(Z) quasi-representations are at most linear in the defect, and the all-MF branch forces them to be exactly linear
distinct_from:
  deligne-sep8-first-order-tensor-threshold: that states the all-MF branch as o(|t|) projective models with a moving parameter; this reads the same branch off plain quasi-representations of Sp_4(Z) through an integer winding, proves the winding can never exceed linear order in the defect, and turns the threshold into an explicit linear floor constant 4|k|/(6g-1).
  dadarlat-linear-groups-have-nonzero-h2-windings: that gives some asymptotic homomorphism of Sp_4(Z) with nonzero winding; this shows nonzero windings are only the qualitative half, and that the quantity that decides the all-MF branch is the ratio of the normalized winding to the defect, on which Dadarlat's theorem is silent.
  exel-loring-mark-quantization: that tries to use windings to kill an infinite-order mark in every corona model (the non-MF direction); this runs the opposite direction, from parameter models to windings, and needs no Kazhdan compression data.
  exel-loring-relative-quasirep-invariant: that records the relative invariant; this is a quantitative budget and saturation statement for one fixed relator of Sp_4(Z).
---

**ESTABLISHED** (route `sp4-quasirep-windings-budget-and-saturation-proof`).

**Setting.** `Gamma = Sp_4(Z)`. `b` is the normalized integral covering cocycle of
`deligne-sep7-norm-parameter-closed-subgroup`. `E_infinity = Gamma x_b Z` has central generator `zeta = (e,1)`,
and `P_op` is the parameter group defined in that claim. Hats denote the lifts `g^ = (g,0)`.

**Relator.** Fix `r = prod_{i<=g} [a_i, b_i]` with `prod [a_i, b_i] = 1` in `Gamma` and
`prod [a_i^, b_i^] = zeta^k` in `E_infinity`, where `k != 0`. Such an `r` exists (step 0 of the route).
Its window `W_r` is the finite set of pairs used to evaluate the word:
- `(y, y^-1)` for each letter `y`;
- `(p_j, y_(j+1))` for the partial products `p_j`.

**Winding.** For a unital `pi : Gamma -> U(d)`, put `W_r(pi) = prod [pi(a_i), pi(b_i)]`, with `[A,B] = A B A* B*`.
When `||W_r(pi) - 1|| < 2`, put `kappa_r(pi) = (1/2 pi i) Tr log W_r(pi)`, using the principal branch. This is an
integer, since `det W_r(pi) = 1`. It is Dadarlat's winding number.

For a finite window `W` containing `W_r`, set

```text
S_W(eps) = sup { |kappa_r(pi)| / d :  d >= 1,  pi : Gamma -> U(d) unital,
                 ||pi(g)pi(h) - pi(gh)|| <= eps on W }.
```

1. **Budget.** For `eps <= 1/(6g-1)`, `S_W(eps) <= (6g-1) eps / 4`.
2. **Parameter models wind at their parameter.** Suppose `U(e) = I` and
   `||U(g)U(h) - exp(2 pi i t b(g,h)) U(gh)|| <= eta` on `W_r`, with `|kt| <= 1/4` and `(6g-1) eta <= 1`. Then
   `kappa_r(U)` is defined, and

   ```text
   | kappa_r(U) - k t d | <= (d/pi) arcsin((6g-1) eta / 2) <= (6g-1) d eta / 4.
   ```
3. **Saturation.** If `P_op = R/Z`, then for every finite `W` containing `W_r`,

   ```text
   limsup_{eps->0} S_W(eps)/eps >= |k| / (2 pi B_W) > 0,    B_W = max_W |b|.
   ```

   The windings are then of the maximal order allowed by item 1.
4. **Explicit floor.** Let `f_W(t)` be the fixed-window projective defect of `deligne-sep8-first-order-tensor-threshold`.
   If `S_W(eps) = o(eps)`, then

   ```text
   liminf_{t->0} f_W(t) / |t|  >=  4|k| / (6g-1),
   ```

   and `P_op = (1/m)Z/Z` for one even `m`.
5. **Where Dadarlat stands.** Dadarlat's Theorem 3.2, as recorded in
   `dadarlat-linear-groups-have-nonzero-h2-windings` and applied to the class of `r`, gives only that `S_W(eps) > 0`
   for every `eps > 0` and every `W`. This refutes the naive target "`S_W` vanishes near `0`". It is compatible
   with both `S_W(eps) = o(eps)` and saturation. It would give saturation only if its quasi-representations had
   dimension `d_n = O(1/eps_n)`, which its proof (from quasidiagonality) does not control.

**What this changes.** Dadarlat's established nonzero `H_2` windings on `Sp_4(Z)` do not refute the triple-cover
target. The quantity that matters is the ratio of normalized winding to defect:
- item 1 bounds it above for every quasi-representation;
- item 3 shows the all-MF branch forces it to stay bounded below along some sequence;
- item 4 shows that if it tends to zero, `P_op` is finite.

The last alternative is recorded as the open prerequisite `sp4-quasirep-windings-are-sublinear`.

DERIVATION
sp4-quasirep-windings-budget-and-saturation-proof
