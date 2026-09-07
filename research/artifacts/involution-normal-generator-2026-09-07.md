# One involution normally generates the rank-four elementary group

External review of the 24-page manuscript, 2026-09-07.  Only the first of
its seven items carries a fact the graph did not already hold; this file
records the verification of that one and the sweep that retired the other
six, so no later session re-ingests them.

## The new fact, checked by hand

Let `R` be a nonzero unital ring, `m >= 4`, and let

```text
sigma = P_((12)(34)) = the permutation matrix of (1 2)(3 4), padded by I_(m-4).
```

**Membership.**  With `w_ij = e_ij(1) e_ji(-1) e_ij(1)`, the 2x2 block of
`w_ij` on coordinates `(i,j)` is `[[0,1],[-1,0]]`, so on basis vectors

```text
w_12 : e_1 |-> -e_2,  e_2 |-> e_1
w_34 : e_3 |-> -e_4,  e_4 |-> e_3
w_13^2 = diag(-1, 1, -1, 1)      (it is -I on the (1,3) plane)
```

and applying `w_13^2`, then `w_34`, then `w_12`:

```text
e_1 |-> -e_1 |-> -e_1 |-> e_2
e_2 |->  e_2 |->  e_2 |-> e_1
e_3 |-> -e_3 |->  e_4 |-> e_4
e_4 |->  e_4 |->  e_3 |-> e_3
```

so `w_12 w_34 w_13^2 = sigma`, and `sigma in EL_m(R)`.  Every coefficient is
`+-1`.

**Normal generation.**  With `[a,b] = a b a^(-1) b^(-1)` and
`sigma e_ij(r) sigma^(-1) = e_(sigma(i) sigma(j))(r)`:

```text
[e_13(r), sigma] = e_13(r) . sigma e_13(-r) sigma^(-1) = e_13(r) e_24(-r),
```

the two factors commuting because `2 != 3` and `4 != 1`.  Then
`e_12(1)` commutes with `e_13(r)` (`E_12E_13 = E_13E_12 = 0`) and
`e_12(1) e_24(-r) e_12(-1) = e_14(-r) e_24(-r)` (Steinberg, `1 . (-r)`), so

```text
[e_12(1), e_13(r)e_24(-r)]
  = e_13(r) e_14(-r) e_24(-r) . e_24(r) e_13(-r) = e_14(-r),
```

using that `e_13` and `e_14` commute.  Conjugating by the `w`'s moves the
position `(1,4)` to any `(i,j)`, `i != j`, up to a sign that `r` absorbs.

## Model tests

- `R = 0`: `EL_m(R)` is trivial and `sigma = 1` has order one, not two.  So
  **nonzero** is a real hypothesis and appears in the statement.
- `R = Z/2`: `w_13^2 = I` and `sigma = w_12 w_34`; the identities survive
  unchanged, because no coefficient other than `+-1` and the arbitrary `r`
  occurs.  This is the one case where the existing signed-swap generator is
  also an involution, and the two statements agree there and nowhere else.
- `m = 3`: there is no double transposition, and the single transposition
  `P_(12)` has determinant `-1`, so it is not in `EL_3(R)` unless `2 = 0`.
  The rank bound `m >= 4` is forced, not cosmetic.
- `2` a zero divisor (`R = Z/4`, `R = Z/2 x Z`): nothing in the calculation
  divides by `2`, and `sigma^2 = 1` on the nose, so the order is exactly two
  in cases where the signed swap has order four.

## Formalization

`GroupApproximation/Leavitt/MatrixDiagonalization.lean:220`,
`exists_elementary_signedSwap`, already puts `[[0,-1],[1,0]]` in the rank-two
elementary group.  The rank-four assembly `sigma = w_12 w_34 w_13^2` is three
instances of that fact in disjoint coordinate pairs; the two commutator
identities are Steinberg relations.  Neither is on main yet.  **The claim is
not formalized**; it is an arithmetic strengthening of a formalized
neighbour, not a new analytic input.

## The other six review items were already established

| Review item | Graph node | Verdict |
| --- | --- | --- |
| Kazhdan projection is a norm limit of finite probability averages, via powers of a lazy symmetric average | `kazhdan-projection-is-norm-limit-of-finite-averages`, `kazhdan-projection-norm-limit-of-averages-proof` | already ESTABLISHED, same proof |
| Every nonzero corner of a norm matrix corona is again a norm matrix corona | `matrix-corona-projection-ideal-and-corner-calculus`, display (CI1) | already ESTABLISHED, verbatim |
| Use `B` directly and drop the intermediate finitely generated subring `S` | `universal-seed-group-collapses-elementary-groups` | already ESTABLISHED; its body says "no passage to finitely generated subrings of `R` occurs" |
| `Hom(K_1(R), M) = Hom(GL_n(R), M)` for MF targets | `aut-of-projective-module-max-mf-quotient-is-k1` | already ESTABLISHED, and in the stronger form covering every nonzero projective module |
| One construction for both trace assertions; Clifford defect in one paragraph | `commuting-lamp-defect-survival-proof`, `kun-thom-clifford-extension-not-weak-mf-via-central-sign` | already ESTABLISHED |
| Compress Lemma 2.1 / 2.8 / simplicity / saturation / reduced-C* consequences | none | editorial only; no proposition changes |

The remaining wording point — that the obstruction is one-sided compression
**together with** a centralizer defect, proper compression alone being
insufficient — is a manuscript-abstract matter, not a graph fact.
