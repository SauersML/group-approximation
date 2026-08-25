---
rg: 2
id: same-center-whitehead-gram-is-not-native-selector-gram
kind: claim
title: The maximal Gram of two same-carrier Whitehead unitaries does not authenticate the unequal native selector occurrences
invalidates:
  - same-center-whitehead-cross-gram-closes-native-two-scale
distinct_from:
  same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps: that correctly constructs the common carrier and computes two adjacent one-quarter swap label actions; this identifies the missing step between those transports and the unequal controlled selector rows.
  unequal-label-ranks-forbid-relational-reservoir-conjugacy: that is a general tensor-factor relational no-go; this audits the specific proposed route and shows that its displayed cross Gram is tautological and has the wrong occurrence type.
  whitehead-swap-copy-completion-retains-rectangular-escape: that gives a finite rectangular model for a Whitehead compression and branch-copy completion; this points directly to the absent selector-groupification row in the same-center argument.
---

**ESTABLISHED REFUTATION OF THE PROPOSED ROUTE.**  In the notation of
`same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`, both
Whitehead words commute with the projection `F`.  Therefore

```text
S_m=F rho(W_m)F : FH -> FH
```

is a unitary for `m=1,2`, and

```text
tau(S_1^*S_2S_2^*S_1)=tau(F).                         (USG1)
```

But `(USG1)` is true for **any** two unitary words which reduce the same
projection.  It contains no information about the rectangular source and
target occurrences of the two controlled selector rows.

The actual normal forms proved for these words are

```text
S_1=SWAP_(1,2) tensor V_1,
S_2=SWAP_(2,3) tensor V_2.                             (USG2)
```

Both fixed label involutions in `(USG2)` have negative fraction `1/4`.  The
affine rank obstruction instead requires operators already authenticated as

```text
T_1=C_(1/4) tensor R_1,
T_2=C_(1/8) tensor R_2,                                (USG3)
```

together with a proof that `R_1,R_2` are the gauges transported by the two
native selector occurrences.  Neither `(USG1)`, `(USG2)`, nor the Coxeter
braid displays a word or operator identity attaching the new one-eighth
label factor in `(USG3)` to `V_2`.  The sentence that the controlled rows
``inherit'' `V_1,V_2` is precisely the open occurrence-typing assertion of
`binary-leavitt-two-shared-gauge-selector-compiler`, not a consequence of
the Whitehead calculation.

Calling the passage a fixed packet relabelling cannot repair it.  Unitary
relabeling preserves the negative spectral multiplicity of the label
involution, so it cannot turn the second one-quarter swap into a one-eighth
selector.  If the one-eighth controlled label is adjoined as a separated
tensor packet, `unequal-label-ranks-forbid-relational-reservoir-conjugacy`
shows that exact group-relational cancellation cannot make it inherit the
conjugate reservoir gauge.

Finally, `opnorm-packet-exactification-is-dimension-free` concerns
operator-norm packet perturbations and does not manufacture the missing
normalized-HS occurrence row.  Even granting exactification of the fixed
Pauli packet, `(USG1)` remains the full-unitary tautology above.

Thus the same-center construction establishes a positive common carrier and
an exact braid for two equal-rank transport gauges, but it does not establish
`(NCG1)` for the prescribed unequal native selector transports.  The native
cross-Gram claim and the non-hyperlinearity goal remain open.

