---
rg: 2
id: kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees
kind: claim
title: The A~2 root-word quotient and the pro-p Iwahori can first differ only where the Iwahori Lie algebra has a minimal relation, i.e. at the Serre degree or a Kassel degree 3mp
distinct_from:
  kms-hc1-a2-pro-p-completion-is-iwahori-criterion: that claim gives the criterion phi^ iso iff towers agree iff r(I_1)<=9, towers through class 30, and one Kassel cocycle at height 3p. This claim bounds every tower deviation by the Lie-algebra H_2 of the Iwahori algebra, gives the Kassel classes at every 3mp, computes all minimal Lie relations in a range, and extends the certified agreement to class 59 (p=5), 62 (p=7) and 65 (p=11).
artifacts:
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2loop.py
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/pqtower.sh
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/towers.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p3.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p5_d130.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p7_d130.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p11.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p13.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p17_d105.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p19_d117.out
  - experiments/kms-hc1-iwahori-lie-relations-2026-09-17/h2_p23_d141.out
---

Notation as in `kms-hc1-a2-pro-p-completion-is-iwahori-criterion`: `p` is an
odd prime, `Gamma=Gamma^A2_p=<a,b,c | a^p,b^p,c^p, [a,b] central in <a,b>,
[b,c] central in <b,c>, [c,a] central in <c,a>>`, `phi^: Gamma^_p -> I_1` is
the surjection onto the pro-p Iwahori of `SL_3(F_p[[t]])`, and `P_k` is the
lower p-central series. Let

```text
L_p = n^+(sl_3) + t sl_3[t]   over F_p,
deg(t^n E_ij) = 3n + j - i,   deg(t^n h) = 3n,
```

so `gr_P(I_1) = L_p`, with dimensions `3,3,2` repeating. Let `F` be the free
Lie algebra over `F_p` on `e_1,e_2,e_0` in degree 1, and write
`L_p = F/I` with `e_1 -> E_12`, `e_2 -> E_23`, `e_0 -> tE_31`. The graded
minimal relations of `L_p` are `H_2(L_p)_k = (I/[F,I])_k`. Put
`D_p = {k : H_2(L_p)_k != 0}`.

- **(G) Graded form of Gamma.** On `gr_P(Gamma^)` the p-power operator `pi`
  is zero. So `gr_P(Gamma^) = F/J` for a graded ideal `J <= I`, and
  `gr_P(phi^)` is the quotient map `F/J -> F/I`.
- **(B) Deviation bound.** Suppose `|Gamma/P_j(Gamma)| = |I_1/P_j(I_1)|` for
  all `j <= k`. Then
  `dim gr_k(Gamma^) - dim gr_k(I_1) <= dim H_2(L_p)_k`.
  So if the towers agree through class `c`, they agree through class
  `c' - 1`, where `c'` is the least element of `D_p` above `c`.
- **(K) Kassel classes.** For every odd `p` and every `m >= 1`, the bilinear
  form `omega_m(t^a X, t^b Y) = a tr(XY) [a+b = mp]` is a 2-cocycle on `L_p`
  of degree `3mp` that is not a coboundary. So `dim H_2(L_p)_{3mp} >= 1`,
  and `dim H^2(L_p, F_p) = infinity`. It pairs with
  `HC_1(F_p[t]) = Omega^1/dF_p[t]`, which is spanned by the classes
  `t^{mp-1} dt`.
- **(O) Obstruction to the graded route.** Any argument that bounds
  `r(I_1)` or the tower of `Gamma^` using only the associated graded Lie
  algebra `gr_P(I_1) = L_p` gives no finite bound. The graded relation count
  `dim H_2(L_p)` is infinite by (K), and in each degree `3mp` the central
  extension of `L_p` by `omega_m` is again generated in degree 1 by elements
  satisfying the Serre relations. Lazard's theory of uniform groups does not
  apply either: `I_1` contains the infinite elementary abelian group
  `x_12(F_p[[t]])`, so it is not p-adic analytic. So `r(I_1) <= 9` needs
  input at group level, namely the vanishing of the Kassel directions in
  `Gamma^`. That input is absent at `p=3`: there the tower deviates at class 6.
- **(C) Computed minimal relations.** `h2loop.py` computes `H_2(L_p)_k`
  exactly (Chevalley--Eilenberg over `F_p`). The nonzero values are
  (degree, dimension):

  | p | degrees computed | nonzero values |
  |---|---|---|
  | 5 | `<= 130` | `(3,6)`, and `(15m,1)` for `m=1..8` |
  | 7 | `<= 130` | `(3,6)`, and `(21m,1)` for `m=1..6` |
  | 11 | `<= 70` | `(3,6)`, `(33,1)`, `(66,1)` |
  | 13 | `<= 80` | `(3,6)`, `(39,1)`, `(78,1)` |
  | 17 | `<= 105` | `(3,6)`, `(51,1)`, `(102,1)` |
  | 19 | `<= 117` | `(3,6)`, `(57,1)`, `(114,1)` |
  | 23 | `<= 141` | `(3,6)`, `(69,1)`, `(138,1)` |
  | 3 | `<= 24` | `(3,6)`, `(6,6)`, `(9,7)`, `(12,6)`, `(15,6)`, `(18,7)`, `(21,6)`, `(24,6)` |

  So, in these ranges and for `p>=5`, `D_p = {3} + {3mp}`. Each Kassel
  degree carries exactly one relation, and the lower bound (K) is sharp. The
  degree-3 classes are the six Serre relations. For `p=3`, the tower
  (T3) of the criterion claim leaves the `I_1` pattern at class 6 with excess
  `8-2=6 = dim H_2(L_3)_6`. So the bound (B) is attained there, which
  calibrates it.
- **(T) Towers through a Kassel degree.** With the standalone ANU `pq`
  (`pqtower.sh`), the increments of `Gamma^A2_p` are exactly `3,3,2`
  repeating through class 50 for `p=5` (order `5^134`), through class 45 for
  `p=7` (order `7^120`) and through class 35 for `p=11` (order `11^94`). This
  covers the Kassel degrees 15, 30 and 45 for `p=5`, 21 and 42 for `p=7`, and
  33 for `p=11`. In each of them the one Kassel
  direction of (C) dies in the group.
- **(Cons) Certified agreement.** Combining (B), (C) and (T):
  `|Gamma/P_k| = |I_1/P_k|` for `k <= 60` (`p=5`), `k <= 63` (`p=7`) and
  `k <= 66` (`p=11`).
  By criterion (R) of `kms-hc1-a2-pro-p-completion-is-iwahori-criterion`,
  every p-group image of `Gamma^A2_p` of p-class `<= 59` (`p=5`), `<= 62`
  (`p=7`) or `<= 65` (`p=11`) factors through `I_1` and kills `w_p`. Before, these bounds were
  class 30. The same argument with the tower of that claim gives class
  `<= 38` for `p=13` (through class 20, first Kassel degree 39).

Scope and what stays open. (B), (G) and (K) are proved for every odd `p`.
(C) and (T) are finite certificates in the stated ranges. Two statements are
not claimed here:

1. for all `p>=5`, `D_p = {3} + 3pN` with dimensions 6 and 1 (a Serre plus
   `HC_1` description of `H_2(L_p)`);
2. every Kassel direction dies in `Gamma^`.

A remark on statement 1 (not claimed). Let `L_Z` be the Chevalley `Z`-form
with `L_p = L_Z (x) F_p`. If `L_Z` is generated in degree 1 over `Z`, then
`H_1(L_Z)=Z^3`. The universal coefficient theorem then gives
`H_2(L_p) = H_2(L_Z) (x) F_p`. So statement 1 says: the torsion of
`H_2(L_Z)_{3n}` has p-part `Z_p/n` for every `p>=5`, and there is no other
torsion prime to 6. That is exactly the p-part of `HC_1(Z[t])_n = Z/n`. This
is what the Kassel--Loday theorem for `sl_3(Z[t])` predicts, and the data in
(C) matches it.

Together they would give `phi^` iso and `r(I_1)<=9` for all `p>=5`, and
therefore the regularity gate for p-group images. By (B), statement 2 can be
checked one degree at a time: it is the tower equality at the classes
`3mp`. A heuristic reason to expect it: the group-level analogue of `HC_1`
is relative `K_2`, and the relative `K_2(F_p[t]/t^n,(t))` vanishes
(Hesselholt--Madsen). Via the Dennis--Stein identity
`<t^a,t^b> = <t^{a+1},t^{b-1}><t^{mp-1},t>`, the Kassel increment
`t^{mp-1}dt` corresponds to a symbol that is trivial in `K_2`.

Proof: `kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees-proof`.
