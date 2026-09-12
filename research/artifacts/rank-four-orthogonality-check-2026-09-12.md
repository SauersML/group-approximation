# Check (i) of the rank-four plan: can T_i S_j = delta_ij e be derived?

Lane `w4-r4-orth`, family R4 (lead `w3-strategist-gate`, verifier `w4-vf-gate`), 2026-09-12.
Target: check (i) of `rank-four-isometry-relations-give-corner-cuntz-family`, Plan 1 of
`research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md`.

**Verdict.** Check (i) fails for both placements the plan admits. Nothing about the gate is decided.

- **Section 1.** By the endpoint `toeplitz-isometry-defects-have-total-rank-at-least-one`, three
  approximate relations and a lower bound on `rk(e)` are all the route needs. So any derivation
  of them from `D != 0` has to be sound in some rank ultraproduct with `D != 0`.
- **Section 2.** The literal placement lives in `UT_4(R)`, which is locally finite:
  - creation data on `(1,2), (2,3)`;
  - annihilation data on `(2,3), (3,4)`;
  - the `x_14` cross frame.

  The sofic-subgroup rank model of `UT_4(R)` has a nonzero defect, and every positive-root
  relation holds exactly in it. So no construction from those data proves (i), exact or
  approximate.

  Two sibling lanes landed this obstruction independently, each with a different model, so this
  artifact records Proposition 2 as a third derivation and adds no node for it:
  - `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` (w4-r4-adversary, c6697aa47b);
  - `unitriangular-data-cannot-assemble-corner-leavitt-families` (w4-heisenberg, f576dccf26).
- **Section 3.** The opposite-root placement at index 3 satisfies an exact identity. Relation (i)
  holds there only modulo a same-row product and a reversed root product. The identical identity
  holds in `EL_3` with index 4 replaced by 2, so the fourth index gives it no new room.

## 0. Conventions

- **Setting.** `R` is a unital ring and `sigma : EL_4(R) -> M^x` a homomorphism into a unital
  ring. Write `X_ij(r) = sigma(x_ij(r))` and `n_ij(r) = X_ij(r) - 1`.
- **Commutators.** `[g, h] = g h g^-1 h^-1`, so `[x_ij(r), x_jk(r')] = x_ik(r r')` for distinct
  `i, j, k`.
- **Commuting roots.** `x_ij(r)` and `x_kl(r')` commute when `j != k` and `i != l`.

**Swap identity (Sw).** For distinct `i, j, k` and `r, r'` in `R`,

```text
n_ij(r) n_jk(r') = n_jk(r') n_ij(r) + n_ik(r r') X_jk(r') X_ij(r) .
```

*Proof.* In the group, `x_ij(r) x_jk(r') = [x_ij(r), x_jk(r')] x_jk(r') x_ij(r) = x_ik(r r') x_jk(r') x_ij(r)`.
Apply `sigma` and put `X = n_ij(r)`, `Y = n_jk(r')`, `Z = n_ik(r r')`.
- The left side is `1 + X + Y + XY`.
- The right side is `(1 + Z)(1 + Y)(1 + X) = 1 + X + Y + YX + Z(1 + Y)(1 + X)`.

Cancel `1 + X + Y`. No characteristic assumption is used, and no commutation of `Z`. QED

In characteristic two this is a companion of the defect factorization
`n_ik(ab) = XY + (1 + X)(YX)(1 + Y)` of `el3-two-root-violation-splits-over-leavitt-branches`.

**Honest models.** The honest case is `M` containing `M_4(C)` with
`sigma(x_ij(r)) = 1 + rho(r) E_ij` for a unital ring homomorphism `rho : R -> C`. There every
product `n_ab(r) n_cd(r')` with `b != c` vanishes.

## 1. The endpoint

`w4-r4-approx` established `toeplitz-isometry-defects-have-total-rank-at-least-one`. For a Sylvester
rank function, an idempotent `e`, and `S_0, S_1, T_0, T_1` in `eAe`,

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0) .
```

The exact case is direct finiteness of the corner.
- **Step 1.** `T_1 S_1 = e` forces `S_1 T_1 = e`.
- **Step 2.** So `S_0 = e S_0 = S_1 T_1 S_0 = 0` when `T_1 S_0 = 0`.
- **Step 3.** Then `T_0 S_0 = 0`, which is not `e`.

Section L1 of the plan artifact already records that check (ii) is not needed.

What this means for check (i):
- a construction of `e, S_j, T_i` whose three defects total less than `rk(e)` cannot exist in any
  rank ultraproduct;
- so deriving one from `D != 0` is exactly proving `D = 0`;
- so each candidate derivation below is judged by whether it could be sound in some rank
  ultraproduct with `D != 0`.

## 2. The positive-root placement is dead

The plan builds the `S_j` from creation data on `(1,2), (2,3)` and the `T_i` from annihilation
data on `(2,3), (3,4)`. Its ingredients:
- `A_i = n_12(t_i)`, `B_j = n_23(s_j)`, `A'_i = n_23(t_i)`, `B'_j = n_34(s_j)`;
- the isometry commutators on both frames;
- the two readings of `x_14(abc)`.

All of these elements lie in `U = UT_4(R)`.

**Proposition 2.** Let `R` be an `F_2`-algebra and `U = UT_4(R)`.
1. `U` is locally finite, hence sofic.
2. There is a homomorphism `tau : U -> M^x` into a rank ultraproduct over `F_2` with
   `rk((tau(x_23(1)) - 1)(tau(x_12(1)) - 1)) = 3/8`.
3. In that `M`, every idempotent `e` with `rk(e) > 0` and all `S_0, S_1, T_0, T_1` in `eMe`
   satisfy `rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0) >= rk(e)`.

*Proof.*
1. Every element of `U` is `1 + N` with `N` strictly upper triangular and `N^4 = 0`, and
   `(1 + N)^4 = 1 + N^4 = 1` because `2 = 0` in `R`. So `U` is nilpotent of class 3 with exponent
   dividing 4. A finitely generated nilpotent torsion group is finite, and locally finite groups
   are amenable, hence sofic.
2. `g = x_12(1)` and `h = x_23(1)` are involutions, and `(gh)^2 = 1 + E_13 != 1`, so `gh` has
   order 4 and `<g, h> = UT_3(F_2)` is dihedral of order 8. Apply Theorem G
   (`sofic-subgroups-carry-rank-models-violating-two-root-identity`; Section 6.4 of
   `research/artifacts/el3-two-root-identities-2026-09-12.md`) to `S = U`.
3. This is the endpoint of Section 1.

QED

**What this kills.** Under `tau`:
- every relation among the plan's positive-root data holds exactly;
- the defect `N_23 N_12` has rank `3/8`;
- no corner family with small defects exists.

So take any argument producing, from `sigma|U` and `N_23 N_12 != 0`, elements `e, S_j, T_i` whose
three defects total less than `rk(e)`. It doesn't matter whether `S_j, T_i` are polynomials in the
root data or use inner inverses, support idempotents, or any other operation available in a rank
ultraproduct. The argument applies verbatim to `tau` and reaches a false conclusion.

A proof of check (i) must therefore use `sigma` on elements outside `UT_4(R)`, meaning opposite
roots or Weyl elements, jointly on a nonsofic subgroup, as
`sofic-subgroups-carry-rank-models-violating-two-root-identity` already demands.

The plan's list of evasions misses this. "It uses the Leavitt relations" does not escape: inside
`U` those relations enter only through commutators, and `U` is locally finite whatever the
coefficient ring.

**Remark 2.1 (polynomial placements, any ring).** Let `M` be any `F_2`-algebra and
`sigma : U -> M^x` any homomorphism. The unital subalgebra generated by `sigma(U)` has no
idempotents other than `0` and `1`.
- **Why.** Finitely many of its elements lie in the image of `F_2[P]` for a finite 2-subgroup `P`
  of `U`. That group ring is local, and so is every nonzero quotient of it.
- **With `e = 1`.** `T_1 S_1 = 1` makes `S_1` and `T_1` units of that local image. So
  `T_1 S_0 = 0` forces `S_0 = 0`, and then `T_0 S_0 = 0 != 1`.

So no placement polynomial in positive-root data satisfies (i) exactly, in any ring. This is the
positive-root case of the Kaplansky calibration L4a.

**Remark 2.2 (odd characteristic, not a node).** For an `F_p`-algebra with `p` odd, `U` has
exponent dividing `9` (p = 3) or `p` (p >= 5), so it is again locally finite. The proof of
Theorem G uses only a finite subgroup acting freely on good points. With `UT_3(F_p)` in place of
`D_8`, it gives a rank model in which `rk(N_23 N_12)` is the normalized rank of left
multiplication by `(h - 1)(g - 1)` on `F_p[UT_3(F_p)]`. That rank is positive, because
`1, g, h, hg` are distinct. I have not computed the exact value.

## 3. The opposite-root placement at index 3, fixed

**Definition (answering L3 of the plan artifact).** For `a, b` in `R`, put

```text
S(b) = n_31(b) n_13(1),     T(a) = n_34(a) n_43(1),     P_3 = n_31(1) n_13(1) .
```

- **The corner.** Let `e` be an idempotent of `M` with `eM = P_3 M`. It exists because `M` is
  regular.
- **The family.** `S_j = e S(s_j) e` and `T_i = e T(t_i) e`.
- **What is checked.** The endpoint L1 is evaluated on `e, S_j, T_i`.

The placement uses the roots `(3,1), (1,3)` and `(3,4), (4,3)`: two root pairs sharing index 3.

**Honest check.** Suppose `sigma(x_ij(r)) = 1 + rho(r) E_ij` with `rho : R -> C` unital. Then:
- `S(b) = rho(b) E_33`, `T(a) = rho(a) E_33` and `P_3 = E_33`, so `e = E_33` is a valid choice;
- `T_i S_j = rho(t_i s_j) E_33 = delta_ij e`;
- `S_0 T_0 + S_1 T_1 = e`;
- `rk(e) = rk(N_13)`.

**Proposition 3 (exact identity, any rings, any characteristic).** For every homomorphism
`sigma : EL_4(R) -> M^x` and all `a, b` in `R`,

```text
T(a) S(b) = n_31(ab) W(a,b) n_13(1) + Delta_row(a,b) + Delta_rev(a,b),

W(a,b)         = X_41(b) X_34(a) X_31(b) X_43(1),
Delta_row(a,b) = n_31(b) n_34(a) n_43(1) n_13(1),
Delta_rev(a,b) = n_41(b) n_34(a) X_31(b) X_43(1) n_13(1).
```

*Proof.*
1. Apply (Sw) at `(i,j,k) = (4,3,1)` with `r = 1`, `r' = b`:
   `n_43(1) n_31(b) = n_31(b) n_43(1) + n_41(b) X_31(b) X_43(1)`.
2. Hence `T(a) S(b) = n_34(a) n_31(b) n_43(1) n_13(1) + n_34(a) n_41(b) X_31(b) X_43(1) n_13(1)`.
3. `x_34(a)` and `x_31(b)` commute (`4 != 3` and `3 != 1`), so the first term is `Delta_row(a,b)`.
4. Apply (Sw) at `(i,j,k) = (3,4,1)` with `r = a`, `r' = b`:
   `n_34(a) n_41(b) = n_41(b) n_34(a) + n_31(ab) X_41(b) X_34(a)`. Substituting turns the second
   term into `Delta_rev(a,b) + n_31(ab) W(a,b) n_13(1)`.

QED

**Consequences.**
1. **Cross terms.** When `t_i s_j = 0`, `n_31(0) = 0`, so `T(t_i) S(s_j) = Delta_row + Delta_rev`
   exactly.
2. **Block-support failures.** `Delta_row` contains the same-row product `n_31(b) n_34(a)`, and
   `Delta_rev` the reversed product `n_41(b) n_34(a)`.
   - Both are products `n_ab(r) n_cd(r')` with `b != c`. For unit coefficients, condition 2 of
     `el3-unit-root-matrix-units-iff-two-root-identities` kills exactly this type.
   - Both vanish in honest models.
3. **The circular shape.** Let `pi : F[EL_4(R)] -> M_4(R)` be the natural representation, extended
   linearly, and extend `sigma` linearly too.
   - `pi` kills both deviation products.
   - `pi` sends the main term to `ab E_33`, because row 1 of `pi(W(a,b))` is the first unit row.

   So for the uncompressed products, each relation of (i) is the honest value plus `sigma` of an
   element of `ker pi`. That is the shape of the baseline candidate in Section L3. By L4a no
   group-algebra identity finishes the check. The deviation terms have to be made small through
   the rank of `M`, and bounding them under `D != 0` is the gate.
4. **No use of the fourth index.** Replace index 4 by 2 throughout, with `T'(a) = n_32(a) n_23(1)`.
   The same proof gives the identical identity inside `EL_3(R)`: (Sw) at `(2,3,1)` and `(3,2,1)`,
   and `x_32(a)` commutes with `x_31(b)`. So this placement reproduces the rank-three telescoping
   of `leavitt-isometry-commutators-constrain-el3-rank-models` Section 2. The fourth index adds no
   room to it.

**Remark 3.1 (a cross term is not forced by its own coefficients).**
- **Setup.** Let `S = M_2(F_2)`, `t_1 -> E_22`, `s_0 -> E_11`, so `t_1 s_0 = 0`. Let
  `G = EL_4(S) = SL_8(F_2)`, and let `sigma` be its left regular representation over `F_2`.
  `D != 0` there.
- **The cross term.** `T(t_1) S(s_0)` is left multiplication by `(a - 1)(b - 1)(c - 1)(d - 1)`, with
  `a = x_34(E_22)`, `b = x_43(1)`, `c = x_31(E_11)`, `d = x_13(1)`.
- **Why it is nonzero.** No nonempty ordered sub-product of `a, b, c, d` equals `1`:
  - two distinct root elements never multiply to `1`;
  - `ab = 1 + E_22 E_34 + E_43 + E_22 E_33` equals neither `c` nor `d`;
  - `ac = 1 + E_22 E_34 + E_11 E_31` is not `d`;
  - `bc = 1 + E_43 + E_11 E_31 + E_11 E_41` is not `d`;
  - `dc = 1 + E_13 + E_11 E_31 + E_11 E_11` is not `ab`.

  So `1` has coefficient `1` in the expansion, the element is nonzero, and so is the cross term.
- **Consequence.** The vanishing of `T(t_1) S(s_0)` does not follow from the Steinberg relations
  and `t_1 s_0 = 0` alone. The joint Leavitt relations have to enter, just as
  `fd-represented-coefficients-violate-two-root-identities` shows for the identity itself.

## 4. Where check (i) stops

- **Positive-root data.** Dead, by Proposition 2.
- **Opposite roots at index 3.** Relation (i) is the honest value plus two block-support deviation
  terms (Proposition 3).
  - For exactness, the deviation terms must vanish.
  - For L1, the corner images of the three defects must total less than `rk(e)`.
  - No Steinberg identity controls these terms, and the fourth index does not enter.
- **Absorbing the deviations into a smaller corner.** Cutting down reproduces the problem rather
  than removing it (guidance only, not a claim):
  - in a nontrivial model the identity fails on the unit pair and on every cylinder corner at
    once (`two-root-identity-is-corner-local-for-leavitt-rank-models`);
  - the defect piece carries an injective rank model of `R^x`
    (`leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model`).
- **What a working construction needs.** None of these is known, so check (i) is open only in
  the sense that its content is the gate:
  - opposite roots, used jointly on a nonsofic subgroup;
  - the regularity or rank of `M` at some intermediate step (L4a);
  - a mechanism, not reducible to Steinberg telescoping, that bounds `Delta_row` and `Delta_rev`
    under `D != 0`.
