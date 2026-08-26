---
rg: 2
id: gkmp-hypotheses-met-on-inf-via-mihailova-ambient
kind: claim
title: With the Mihailova product-of-free-groups ambient, every GKMP amalgam hypothesis is automatic on the INF branch, isolating the amalgam-vs-HNN tension as the sole obstruction
distinct_from:
  fp-forces-hnn-edge-into-free-entropy-obstruction: that states the amalgam/HNN dichotomy abstractly; this shows the amalgam side's hypotheses are all discharged for a concrete compiler, so the ONLY thing missing is the finite-presentation (HNN) form.
  gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability: that listed separability (SEP) as an unverified condition; this proves (SEP) is automatic on the branch where it is needed.
---

ESTABLISHED (as a discharge of GKMP Theorem 1.1's hypotheses; each clause is
proved).

Use the Mihailova benign compiler
[[mikhailova-fiber-product-gives-regular-mf-benign-compiler]]: for the
recursive family `N_e normal F` it outputs a benign witness

```text
K_e = F(A) x F(X_e) x F(X_e),   L_e = F(A) x M_e,
i_e(F) cap L_e = i_e(N_e),                                            (M1)
```

`M_e <= F(X_e) x F(X_e)` the Mihailova fiber product of `H_e = F/N_e`'s Higman
embedding.  Run the Higman rope on this witness with input group `C = F/N_e`.
For GKMP Theorem 1.1 ([[gkmp-amalgam-product-mf-permanence]]) applied to the
amalgam `K_e *_{L_e} (L_e x C)` the four hypotheses are:

1. **`K_e` is MF.**  `K_e` is a direct product of finite-rank free groups.
   Free groups are MF and exact; a direct product of MF groups with one
   exact factor is MF; so `K_e` is MF.  (It is even PFF: a product of free
   groups is a RAAG, hence virtually special, hence PFF by GKMP Cor 1.4.)

2. **`K_e` is exact.**  Free groups are exact and exactness is closed under
   direct products, so `K_e` is exact; the exactness hypothesis of Theorem
   1.1 is met on the `K_e` side outright.

3. **`C` is residually finite MF on `INF`.**  With the exact switch on the
   two-generator bridge, `C = B2(1)` is residually finite
   ([[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]), hence
   MF.

4. **`L_e` is separable in `K_e` on `INF`.**  Separability of `L_e` in `K_e`
   is equivalent to separability of `N_e = i_e(F) cap L_e` in `F`, which is
   equivalent to `F/N_e = C` being residually finite.  On `INF`, `C = B2(1)`
   is residually finite, so `L_e` is separable in `K_e`.  (On `FIN`, `C`
   contains `E` and is not residually finite, so `L_e` is *not* separable
   there -- but on `FIN` we want non-MF, which needs no GKMP.)

Therefore, on the `INF` branch, **all hypotheses of GKMP Theorem 1.1 hold**,
and the amalgam

```text
K_e *_{L_e} (L_e x C)   is MF     (on INF).                           (M2)
```

## What this leaves

The amalgam `(M2)` is MF but not finitely presented (`C` is only recursively
presented).  The finitely presented Higman output is the **rope HNN**
`< K_e x C, s | s(l,1)s^-1 = (l, Phi(l)), l in L_e >`, and it does not embed
in `(M2)`: a conjugator would have to carry `L_e <= K_e` to `graph(Phi) <=
L_e x C`, subgroups of different vertex groups of the amalgam, not conjugate
there.  So the **sole** remaining obstruction is the amalgam-vs-HNN tension
of [[fp-forces-hnn-edge-into-free-entropy-obstruction]]: the stable letter
needs the two-model conjugacy of `L_e` that free entropy obstructs.

This discharges the separability worry entirely and shows the difficulty is
concentrated in one place: turning the (now fully justified) MF amalgam into
a finitely presented group without a stable letter, or proving the HNN form
of GKMP for this specific rope data.

## Consequence: the negative-answer exit is constrained

Because hypotheses 1--4 all hold on `INF`, any proof that MF is *not*
finite-presentation `Pi^0_2`-complete cannot come from the amalgam being
non-MF; it would have to exploit that the finitely presented HNN is strictly
harder than its MF amalgam completion, i.e. that finite presentability itself
destroys MF here.  That is a sharper and more specific target than a generic
non-completeness argument.
