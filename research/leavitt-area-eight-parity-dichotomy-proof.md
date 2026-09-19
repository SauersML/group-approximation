---
rg: 2
id: leavitt-area-eight-parity-dichotomy-proof
kind: route
title: Eliminate the 36 even residuals and spend the 24 corners among odd faces
target: leavitt-area-eight-parity-breaking-dichotomy
requires:
  - leavitt-even-region-short-atlas-has-area-ten
---

The 36 shortest residuals in the even-region census all have `Q`-length
eight.  Expand `h_1=q_0p_1` and `k_2=p_0e_1`, combine adjacent syllables in
the same free factor, and use

```text
q^2=a^2=e^2=1,   [a,e]=[a,q]=[e,q]=1.
```

In every case at least one alternating `G_0/G_1` syllable remains; each is
nonidentity by its root support (the basic one is
`a_0p_1^(-1)e_0p_1`).  Free-product normal form proves that none of the 36
words vanishes.

Length one is immediate.  For length three, split by the number of bridge
labels `h_1^(+-1),k_2^(+-1)`.  With no bridge, the word lies in
`V_4(h_0,h_2)*V_4(k_0,k_1)`, which has no odd relation.  With a bridge,
expansion leaves an uncancelled `p_0^(+-1)` or `p_1^(+-1)` syllable unless
the other two letters are the inverse bridge pair; in that exceptional
case the word reduces to a conjugate of one nontrivial gate label.  Thus no
length-three identity exists.

Now let the five internal face lengths be `d_1,...,d_5` and the outer length
be `d_0`.  Trivalence and Euler give

```text
sum_(i=0)^5 d_i=24.                                      (PDP1)
```

The number of odd `d_i` is even.  If at least two INTERNAL faces are odd
and every such face had length at least nine, then already in the cheapest
case of two odd internal faces,

```text
sum d_i >= 9+9+2+2+2+2 = 26,
```

contradicting `(PDP1)`.  Hence one has length five or seven.  If exactly one
internal face is odd, parity forces the outer face odd.  The other four
internal faces have length at least two and the outer has length at least
one, so the odd internal length is at most `24-8-1=15`.  Together with the
length-one/three exclusion this gives precisely
`{5,7,9,11,13,15}`.

