---
rg: 2
id: returned-opposite-cross-zero-has-finite-s6-model
kind: claim
title: The returned opposite cross-zero cell has a finite S6 holonomy model
invalidates:
  - returned-a2-fold-window-places-native-pauli-factors
artifacts:
  - research/returned-opposite-cross-zero-s6-proof.md
distinct_from:
  relative-a2-weyl-orbit-has-seven-state-gauge-model: that cycles the canonical payload through two fresh reservoir supports and does not compare the returned packet with its overlapping source; this adds the direct source opposite-root cross-zero comparison after return.
  reverse-product-whitehead-fold-has-finite-fusion: that uses three scalar support packets and omits the cross-zero between opposite factors from different children; this uses a single non-scalar S6 packet satisfying both cross-child opposite rows and the nonlinear parent Whitehead fold.
  native-opposite-arm-return-has-finite-s6-model: that authenticates one branch through a partial Whitehead and final return; this contains both child reverse-product Whiteheads and their parent-generation relation in one finite Coxeter packet.
---

**ESTABLISHED GENUINE-RETURN FINITE FENCE.**  After the native `A_2` orbit
returns the branch-one coefficient occurrence, the smallest ordinary source
comparison is

```text
[D_0,C_1]=1,
D_0=x_41(q_0),                 C_1=x_14(q_1).          (ROC1)
```

This is a valid fixed Steinberg/Leavitt word.  Direct block multiplication
proves it from `q_0q_1=q_1q_0=0`; the symmetric companion
`[D_1,C_0]=1` is valid as well.  Thus `(ROC1)` compares the returned packet
with the original source packet and is stronger than `H^3=1`.

It still does not force coefficient multiplication in an arbitrary finite
group occurrence model.  In `S_6` put

```text
C_0=(1 2),          D_0=(2 3),          W_0=(1 3),
C_1=(4 5),          D_1=(5 6),          W_1=(4 6),     (ROC2)
J  =(1 2)(4 5),     D_A=(2 3)(5 6),     W_A=(1 3)(4 6).
```

Then

```text
C_0C_1=J,
W_i=C_iD_iC_i=D_iC_iD_i,
W_A=JD_AJ=D_AJD_A,
W_0W_1=W_A,                                           (ROC3)
[D_0,C_1]=[D_1,C_0]=1.                                (ROC4)
```

All child and parent opposite-root Whitehead words, the nonlinear
completeness comparison, and both returned cross-zero words are exact, while
`J!=1`.  The two branches occupy disjoint Coxeter triples inside one
non-scalar permutation packet; their parent is the diagonal product.

The full relative `A_2` occurrence orbit can be adjoined by taking three
coordinate copies of this finite packet and letting the native order-three
label word cyclically permute them.  Its third power returns every named
occurrence exactly, and `(ROC2)--(ROC4)` hold coordinatewise in the returned
copy.  The regular representation of the finite semidirect product keeps
the parent mark nontrivial.

Therefore the ordinary return word exists and does not contradict the
regular representation, but it still does not establish `(BAC1)`.  A
further relation would have to identify the cross-child opposite factors
with the canonical noncommuting factors on one irreducible payload block;
valid returned zero-product words permit the finite Coxeter re-gauging above.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis, or
literature result is used.

DERIVATION
returned-opposite-cross-zero-s6-proof
