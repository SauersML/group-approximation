---
rg: 2
id: involutive-schreier-alternating-form-gap-proof
kind: route
title: Polarize a sampled quadratic form into the independent-pair Schreier gradient
target: involutive-schreier-matchings-uniformly-kill-alternating-commutator-forms
requires: []
---

Let `Omega_2` be the ordered pairs `(x,y)` of linearly independent vectors.
It is one transitive `GL(V)`-set.  On its normalized `ell^2` space define

```text
F_B(x,y)=(-1)^B(x,y).                                         (SG1)
```

For `s^2=I`, polarization in characteristic two gives

```text
B(sx,sy)+B(x,y)
 = q_s(x+sy)+q_s(x)+q_s(sy).                                 (SG2)
```

Indeed the right side is the polar form of `q_s` at `(x,sy)`:

```text
B(sx,sy)+B(x,s^2 y).
```

If `b` is uniform on `V`, write `delta_s=Pr(q_s(b)=1)`.  On a uniform
independent pair, each of `x` and `sy` is uniform nonzero, while the largest
atom of `x+sy` is at most `8/5` times a uniform atom when `|V|>=8`.
The union bound in `(SG2)` therefore gives

```text
||s F_B-F_B||_2^2
 =4 Pr_(Omega_2)(B(sx,sy)+B(x,y)=1)
 <=16 delta_s.                                                (SG3)
```

It remains to bound the non-invariant mass of `F_B`.  If `B` has rank `2r`
and `q=|V|`, then `rad(B)` has size `q/2^(2r)`.  For every
`x` outside the radical, exactly `q/2` choices of `y` have `B(x,y)=1`, and
all such pairs are independent.  Hence on `Omega_2`,

```text
p:=Pr(B(x,y)=1)
  = (q-q/2^(2r)) q / (2(q-1)(q-2)),
3/8 <= p <= 2/3.                                              (SG4)
```

Since `Omega_2` is transitive, the invariant projection of `F_B` is its
mean.  Therefore

```text
||F_B-P_inv F_B||_2^2=4p(1-p) >=8/9.                          (SG5)
```

Average `(SG3)` over `s`, apply `(IS1)` and `(SG5)`, and obtain

```text
16 delta >= (8/9) lambda,
delta >= lambda/18.
```

Finally, `(IS4)` is the degree-two presentation calculation.  The internal
additive laws identify the mixed degree-two words with `V tensor V`; the
identity relators contribute `b tensor b`.  Their polarization also kills
`x tensor y+y tensor x`, giving precisely the exterior square.
