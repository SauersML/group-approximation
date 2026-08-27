---
rg: 2
id: cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
kind: claim
title: A repeated cross Whitehead sandwiches six branch roots into the signed Hecke normalizer
artifacts:
  - experiments/individual_cross_whitehead_unmatched_plus_root_return_search.py
  - research/cross-whitehead-branch-root-return-enumeration.md
distinct_from:
  individual-cross-whiteheads-miss-native-hecke-target: that proves `K_i` alone is not a signed-Hecke transporter; this inserts one arbitrary depth-one opposite-root word and one nonnormal root, and finds the first exact individual source returns.
  two-depth-one-nonnormal-roots-do-not-return-cross-whitehead: that exhausts two added elementary roots and finds no return; this replaces one of those roots by an arbitrary unmatched three-factor opposite-root word and obtains a complete positive classification.
  signed-hecke-normalizer-has-eight-external-root-returns: that classifies constant-root external normalizers; these returns conjugate nonconstant branch-supported roots through `K_i` into two nonconstant internal normalizer channels.
---

**ESTABLISHED POSITIVE RETURN CLASSIFICATION.**  Let `D_1` be the eight
nonconstant depth-one prefix matrix units, and retain `K_0,K_1`, the signed
pair `(L_0,lambda_0)`, `Q`, and `J_1`.

At any oriented actor root position allow an arbitrary Whitehead-shaped word

```text
W=x_ab(c)x_ba(d)x_ab(c),              c,d in D_1,     (CWR1)
```

without assuming that `c,d` are matched partial inverses.  Also choose one
individually nonnormal root

```text
R=x_ef(g),                              g in D_1,      (CWR2)
```

whose oriented position differs from `(a,b)`.  Test both additional-word
orders `WR` and `RW` before the terminal original `K_i`.

There are `2688` words `(CWR1)` and `304` roots `(CWR2)`.  Removing equal
positions leaves

```text
2688*304-38*64*8=797696                            (CWR3)
```

syntactic candidates per order, branch, and target.  Across both orders,
both branches, and the source/native targets, this is `6381568` words.

The full exact search has precisely `24` source-target hits and no native
target hit.  All source hits have order `WR`; in every one, `W` is one of
the two braid spellings of `K_i`.  After identifying those two spellings,
the six distinct hits for branch zero are

```text
R=x_(8,k)(g),
k in {6,9},                 g in {s_1,r,q_1},          (CWR4)
```

and for branch one they are

```text
R=x_(8,k)(g),
k in {6,9},                 g in {s_0,p,q_0}.          (CWR5)
```

They are genuine source returns because the exact block conjugations are

```text
K_0x_(8,k)(g)K_0=x_(7,k)(pg),
K_1x_(8,k)(g)K_1=x_(7,k)(rg).                         (CWR6)
```

The nonzero coefficient tables are

```text
p{s_1,r,q_1}={s_0,q_0,p},
r{s_0,p,q_0}={s_1,q_1,r}.                             (CWR7)
```

Both output positions `6->7` and `9->7` are signed nonconstant-normalizer
positions.  Hence, if `L=WR=K_iR`, then

```text
LK_i=K_iRK_i in Norm(L_0,lambda_0),
LK_iQK_iL^(-1)=Q.                                    (CWR8)
```

Every displayed relation is verified against all ten signed generators.
There are no full-signature hits for order `RW`, and no candidate in either
order satisfies

```text
J_1^(-1)LK_i in Norm(L_0,lambda_0).                   (CWR9)
```

The enumeration is exhaustive without traversing all `6381568` words.
For each target and order, it hashes the exact Leavitt-matrix image of
`h=x_28(1)` after the first occurrence, crosses only the distinct states
with the second menu, and compares against the precomputed finite sets
`K_iL_0^(+)K_i`.  It executes `1128560` exact compressed transitions,
expands `1700` exposed-row survivors, and applies the remaining nine signed
tests to every survivor.  Classification assertions verify `(CWR4)--(CWR5)`
and both braid spellings explicitly.

This is the first positive individual-`K_i` source return in the bounded
search.  It does not yet give the ungauged ESB bridge: the output
`x_(7,k)(pg)` or `x_(7,k)(rg)` is a nonconstant signed normalizer and may
carry an uncontrolled reservoir action.  A closing relation must type that
returned normalizer against a native occurrence or cancel its gauge; the
full-Gram identity `(CWR8)` alone does not do so.

No Property T, Kazhdan input, trace hypothesis, local computation,
literature theorem, or Lean compilation is used.

DERIVATION
cross-whitehead-branch-root-return-enumeration
