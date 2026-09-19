---
rg: 2
id: middle-index-marked-heisenberg-packet-is-whitehead-equivariant
kind: claim
title: The three middle-index Leavitt pairs form an arbitrary-profile marked Heisenberg packet equivariant under both prefix Whiteheads
artifacts:
  - research/middle-index-marked-heisenberg-whitehead-proof.md
distinct_from:
  nine-pair-marked-heisenberg-regularization-is-selector-spectator: that places q-coefficient cells on spare indices and makes every current selector word commute with them; this packet uses the actual prefix coefficients on indices 7,8,9 and the two Whiteheads act by the two adjacent permutations.
  same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps: that puts q-centered cells on a separate marked-overlap corner; this centers the cells at the mark itself and therefore obtains arbitrary-profile atom balance directly on the full marked sector.
  binary-leavitt-arbitrary-profile-native-cross-gram: that asks for the two unequal controlled selector occurrences and their mixed-Pauli gauge; this gives an exact common Gram only for the literal adjacent prefix-Whitehead words.
---

Put `R=L_(F_2)(1,2)`, `q=s_1t_1`, `z=x_13(q)`, and, for
`m=1,2,3`, put

```text
k_1=7, k_2=8, k_3=9,
a_m=s_1t_(0^m),                 b_m=s_(0^m)t_1,
X_m=x_(1,k_m)(a_m),             Y_m=x_(k_m,3)(b_m).   (MIH1)
```

Then

```text
[X_m,Y_n]=z^(delta_(m,n)),
[X_m,X_n]=[Y_m,Y_n]=[z,X_m]=[z,Y_m]=1.                (MIH2)
```

Thus the seven displayed involutions form a three-pair extraspecial packet
with center the marked root itself.  Notice that the vanishing for `m!=n`
in `(MIH2)` is an **index** statement: the two roots have different middle
indices.  It does not incorrectly assert that the nested Leavitt
coefficients `a_mb_n` vanish.

For `m=1,2`, retain the literal prefix-Whitehead words

```text
c_m=s_(0^(m+1))t_(0^m),       d_m=s_(0^m)t_(0^(m+1)),
W_m=x_(k_(m+1),k_m)(c_m)
    x_(k_m,k_(m+1))(d_m)
    x_(k_(m+1),k_m)(c_m).                              (MIH3)
```

They normalize the packet and act by the adjacent transpositions:

```text
Ad(W_m):(X_m,Y_m)<->(X_(m+1),Y_(m+1)),                (MIH4)
```

fixing the remaining pair and `z`.  In an arbitrary finite-dimensional
unitary representation let `P=(1-rho(z))/2`.  On `PH` the packet algebra is

```text
M_8(C) tensor 1_M.                                    (MIH5)
```

In particular, for every sign vector `epsilon in {+1,-1}^3`,

```text
e_epsilon=P product_m (1+epsilon_m rho(X_m))/2,
tau(e_epsilon)=tau(P)/8                               (MIH6)
```

for every normalized trace profile.  The two constant-sign atoms are fixed
by both adjacent permutations.  If `e=e_(+,+,+)` (or `e_(-,-,-)`), then

```text
e rho(W_i)=rho(W_i)e,
tau((rho(W_1)e)^*(rho(W_2)e)(rho(W_2)e)^*(rho(W_1)e))
 =tau(e)=tau(P)/8.                                    (MIH7)
```

This is an actual arbitrary-profile common positive cross-Gram carrier for
the two literal unequal-prefix Whitehead transports.  It uses only explicit
Steinberg relations and finite-dimensional trace conjugacy, with no
Property `(T)`, Kazhdan input, canonical trace, or literature theorem.

It is not yet the native unequal-selector result.  The action in `(MIH4)`
is the same pair of adjacent three-qubit swaps as before: each has negative
label fraction `1/4`.  Equation `(MIH7)` therefore does not authenticate the
separate controlled `1/8` selector occurrence required by the two-scale
compiler.

DERIVATION
middle-index-marked-heisenberg-whitehead-proof
