---
rg: 2
id: two-distinct-rank-two-channels-cannot-factor-cross-return
kind: claim
title: Two distinct rank-two channels cannot factor an undressed cross-Whitehead return
artifacts:
  - research/two-channel-cross-return-block-proof.md
distinct_from:
  first-cross-whitehead-has-no-alternative-low-depth-return: that solves one elementary-root return and one arbitrary partial Whitehead on the original `(7,8)` pair; this permits two arbitrary invertible coefficient words on two different coordinate pairs.
  two-depth-one-leavitt-roots-return-only-constantly: that enumerates two elementary roots with depth-one monomial coefficients; this is coefficient-independent and includes full Leavitt sums and arbitrary depth-changing rank-two blocks.
  dyadic-cross-whitehead-fusion-has-finite-product-gauge: that factors the coarse word into two suffix pieces in the same `(7,8)` channel; this proves why moving the two factors into distinct stable channels cannot give another factorization.
---

**ESTABLISHED TWO-CHANNEL BLOCK FENCE.**  Work on the stable actor
coordinates and retain

```text
K_0=[[q_1,p],[r,q_0]]                                (TCR1)
```

on `(7,8)`.  Suppose two coefficient-sensitive invertible words `A,B` are
each supported on one rank-two coordinate pair, their pairs are distinct,
and their product is supported on `(7,8)`.  This class includes elementary
roots, arbitrary partial Whiteheads, and coefficient sums or depth-changing
Leavitt units inside either two-by-two block.

Any coordinate outside `{7,8}` which occurs in only one support pair would
survive in the product.  Hence the only nontrivial distinct-pair possibility
uses one common spare coordinate `k`:

```text
supp(A)={k,7},             supp(B)={k,8},              (TCR2)
```

or the reverse order.  On ordered coordinates `(k,7,8)`, write

```text
A=[[a,b,0],[c,d,0],[0,0,1]],
B=[[e,0,f],[0,1,0],[g,0,h]].                          (TCR3)
```

Then

```text
AB=[[ae,b,af],[ce,d,cf],[g,0,h]],                     (TCR4)
BA=[[ea,eb,f],[c,d,0],[ga,gb,h]].                     (TCR5)
```

If either product fixes the `k` coordinate and has no `k`-to-`{7,8}`
entries, its induced `(7,8)` block is necessarily triangular: `(TCR4)` has
lower-left entry zero, while `(TCR5)` has upper-right entry zero.  This uses
only literal block support, not cancellation, a domain assumption, or a
monomial restriction.

The possible undressed signed returns on the original pair are

```text
N K_0,                 N in {1,x_78(1)}.              (TCR6)
```

Their off-diagonal pairs are respectively

```text
(p,r),                    (p+q_0,r),                  (TCR7)
```

and both entries are nonzero.  The two native-target blocks

```text
J_1 N K_0,             N in {1,x_78(1)},              (TCR8)
```

both have off-diagonal pair `(y_1,r)`, again with both entries nonzero.
Therefore none of `(TCR6)` or `(TCR8)` can equal a product of two words in
distinct rank-two channels.

This rules out the smallest stable-index attempt to authenticate two
independent nonnormal occurrences: two different partial Whitehead/root
channels cannot even reproduce the required ordinary group element, before
a reservoir-gauge equation is read.  The same-pair alternative was already
closed by the return equation, and dyadic factors in that same pair are
only coarse/fine fusion.

An arbitrary factorization of `N K_0` with a normalizer word spread over
other actor coordinates is not covered and would in any case have to be
distinguished from normalizer dressing.  A live independent factorization
must use at least three rank-two channel occurrences, or one occurrence
whose literal support already contains three or more coordinates; two
ordinary two-coordinate blocks are impossible.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
two-channel-cross-return-block-proof
