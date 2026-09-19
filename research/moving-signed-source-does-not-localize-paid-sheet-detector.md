---
rg: 2
id: moving-signed-source-does-not-localize-paid-sheet-detector
kind: claim
title: A positive moving signed source does not localize the paid sheet detector
artifacts:
  - research/moving-signed-source-sheet-detector-fence-proof.md
distinct_from:
  paid-cut-has-moving-hecke-source-or-detector: that produces a positive moving subprojection of the actual signed source and one exact Hecke transport; this proves that the newly exposed sheet detector can still act trivially on the whole source and hence on every such subprojection.
  row2-source-factor-detects-paid-pauli-sheet: that proves global nontriviality and marked-rank scale for two literal factor-level sheet detectors; this audits their compression to the moving source and separates global root rank from source incidence.
  el20-order-seven-heads-force-zero-common-hecke-reducing-cut: that forces boundary from any common signed-source cut; this explains why that boundary is not already a typed source-to-native Gram transition.
  paid-t00-reynolds-cut-is-whitehead-reducing: that localizes one paid menu member on a cut reducing both equal-scale Whiteheads; this keeps the frozen forty-eight-word choice but shows that conjugating the signed source by it creates no further occurrence tying the next cut to an unequal native output.
  odd-native-s-factor-return-diamond-has-gl7-model: that authenticates the complete odd factorization of the first native Whitehead and removes its artificial central sign; this observes that the resulting coefficient-sensitive diamond still has a marked GL7 model and is not attached to the moving signed source.
  support-return-gives-gauged-native-loop: that gives odd native identities through prefix-support Whiteheads on a recentered marked carrier; this notes that those words miss the signed source and act as equal quarter swaps on their transported charts.
---

**ESTABLISHED SCOPED LOCALIZATION FENCE.**  Let `R_0<=Q` be any positive
moving source obtained in the source branch of
`paid-cut-has-moving-hecke-source-or-detector`, and put

```text
R_i=u_iR_0u_i^(-1),
u_1=B_2A_1,                 u_2=B_3A_2A_1.             (MSD1)
```

The common-tail sheet detector

```text
K_Q=[A_1,H]=x_43(a_1h)                                  (MSD2)
```

does not have positive compression on `R_0` as a consequence of the
present packet.  The exact four-dimensional signed-character model from
`row2-source-factor-detects-paid-pauli-sheet` has

```text
Q(K_Q-1)Q=0,               zQ=-Q,
z=VK_QV^(-1),              rank_-(z)=rank_-(K_Q)=2.    (MSD3)
```

Therefore, for every `R_0<=Q` in that model,

```text
(K_Q-1)R_0=0,
(u_iK_Qu_i^(-1)-1)R_i=0.                               (MSD4)
```

This remains true even though the detector is globally nontrivial, has the
same spectral rank as the marked involution, `A_1` normalizes the literal
signed source, and `H` has zero source leakage in the model.  Hence neither
global normal saturation nor a sharper use of `A_1Q=QA_1` can turn the
moving-source conclusion into detector incidence.

The coefficient-shorter row-two detector

```text
K=[S_57,H]=[[S_57,D],Y_2]=x_53(s_1h)                  (MSD5)
```

does not repair this.  Its established estimate is a global spectral-rank
comparison.  The occurrence cube contains no relation naming `Q`, and no
current result bounds either `[S_57,Q]` or `Q(K-1)Q`.  Thus compression of
the cube to `R_0`, or after `(MSD1)` to `R_i`, introduces an uncontrolled
`S_57` boundary.  Direct-sum segregation of the signed-source sector and
the exact factor-cube sector is compatible with this displayed occurrence
table: `Q` may be zero on the summand carrying the nontrivial `K`, while
the source summand kills `K`.  This is a scoped finite-table fence, not a
representation of the full Steinberg group; its point is exactly that the
only full-group input currently used for `K` is global normal saturation,
which does not forbid such source segregation without a mixed occurrence.

The order-seven inequality

```text
10||(1-R_0)t_1R_0||_2+4||(1-R_0)t_2R_0||_2
  >=sqrt(tau(R_0))                                      (MSD6)
```

also does not supply the missing row.  It proves that at least one head
exits `R_0`; it names neither the range projection of that exit nor its
quarter/eighth label factor.  Replacing the range by
`t_iR_0t_i^(-1)` makes the Gram equality tautological and leaves the
moving-frame multiplicity coboundary free.

The forty-eight-word paid/Reynolds menu has already done all that its
present typing permits: it chooses the frozen word `s` and hence the moving
source `sQs^(-1)`.  No remaining relation in that menu identifies a
post-`u_i` cut with either unequal native target or makes an odd sheet
factor reduce that cut.

The other authenticated odd occurrences do not fill this slot.  The
primitive mixed-relator audit reaches only the twice-occurring `X_i`
factors.  The returned-root diamond and its odd `X_1Y_1X_1` closure
authenticate `J_1` but close in a marked `GL_7(F_2)` packet with no signed
source attachment or second scale.  The prefix-support returns contain one
odd `J_i`, but move to an alternate Pauli chart on which the label action is
again a quarter swap and which does not preserve `Q`.  Finally the derived
order-seven word is exactly the boundary statement `(MSD6)`, not a
source/range Gram certificate.  Thus every currently named odd occurrence
falls on one of the already fenced sides of `(MSD7)`.

Consequently the exact next input is not another global nonzero root or
another boundary lower bound.  It is one ordinary mixed occurrence `c_i`
and an actual native target cut `F_i` for which, on a positive subcut of
`R_i`, both compressed Grams are charged to ordinary relator defects,

```text
(F_ic_iR_i)^*(F_ic_iR_i)=R_i+o_2(1),
(F_ic_iR_i)(F_ic_iR_i)^*=F_i+o_2(1),                  (MSD7)
```

where `F_i` is typed by the prescribed unequal native row, and for which a
mixed odd-parity square compares the reservoir factor in the fixed Hecke
frame rather than merely conjugating it into the next moving chart.  In
the row-two formulation this must in particular pay/control the
`S_57` boundary or force positive compression of `(MSD5)`.  None of the
currently authenticated ordinary occurrences supplies `(MSD7)`.

No Property `(T)`, canonical trace profile, literature input, local
computation, or Lean compilation is used.

DERIVATION
moving-signed-source-sheet-detector-fence-proof
