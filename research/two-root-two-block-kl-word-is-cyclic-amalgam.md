---
rg: 2
id: two-root-two-block-kl-word-is-cyclic-amalgam
kind: claim
title: Two separated variable blocks coupled to adjacent normal-generating Leavitt roots still reduce to a cyclic amalgam
distinct_from:
  leavitt-normal-root-square-equation-has-amalgam-countermodel: That treats the one-block word r times t-squared; this treats the first separated two-block word with two distinct adjacent root coefficients.
  leavitt-degree-kernel-quotient-tests-are-procyclic: That constrains abstract obstruction quotients; this computes the nonsolvable obstruction quotient for a concrete two-root word.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a successful word; this rules out the shortest candidate using distinct normal-generating root conjugacy data.
---

In `G=L_(F_2)(1,2)^x ~= EL_20(R)`, take the adjacent elementary roots

```text
r=x_12(1),          s=x_23(1).
```

Both are nontrivial involutions and each normally generates `G`.  Their
product `c=rs` has order four.  Nevertheless the degree-two, two-block word

```text
w=r t s t
```

does not normally generate `N_2`.  Its relative quotient and degree-kernel
quotient are

```text
(G*<t>)/<<w>>             ~= G *_(<c>) C_8,
N_2/<<w>>_(G*<t>)         ~= G *_(<c>) G,                 (RTB1)
```

where `<c> ~= C_4` embeds in `C_8` as the subgroup of squares.

Thus even two separated occurrences of the variable and two distinct
normally generating coefficient roots do not make conjugation recover a
coefficient: after the Tietze substitution `y=ts`, the entire equation is
only the root adjunction `y^2=rs`.  Any viable candidate must avoid such a
substitution collapse—for example by using at least three variable blocks or
an asymmetric exponent/sign pattern that cannot be folded into one new root.

