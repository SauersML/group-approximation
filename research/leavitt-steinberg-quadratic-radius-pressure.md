---
rg: 2
id: leavitt-steinberg-quadratic-radius-pressure
kind: claim
title: The affine Leavitt Steinberg group packs p^(2^n) marked dimension pressure into word radius O(n^2)
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that proves the abstract depth-n Heisenberg subgroup and its representation dimension; this bounds the subgroup generators in the fixed finite generating metric of the ambient finitely presented group.
  slofstra-subexponential-hyperlinear-profile: that records Slofstra's quantitative approximation construction; this is the exact word-metric compression supplied by relative Leavitt prefixes, before a robust approximate-representation theorem is asserted.
---

**ESTABLISHED.**

Fix the standard finite generating set of `St_5(L_A(S))` consisting of root
elements over a finite algebra generating set of `L_A(S)`. There is a
constant `C`, depending only on this fixed presentation, such that every
generator `X_alpha,Y_alpha` of the depth-`n` Heisenberg packet in `(LHP3)`
has word length at most

```text
C(n+1)^2.                                                (LWR1)
```

Indeed, Weyl words move a root element between root positions at bounded
cost, and

```text
x_ik(ab)=[x_ij(a),x_jk(b)]                               (LWR2)
```

multiplies two coefficient words. Build a length-`n` coefficient by a
balanced binary multiplication tree. If `L(n)` is the maximum resulting
root-word length, then

```text
L(n)<=4L(ceil(n/2))+C,
```

so `L(n)=O(n^2)`.

Combining `(LWR1)` with `leavitt-prefixes-form-exponential-heisenberg-packet`
shows that a ball of radius `C(n+1)^2` contains a finite generalized Pauli
packet for which every nontrivial active central sector has dimension at
least

```text
p^(2^n).                                                 (LWR3)
```

This is an exact word-metric theorem, not yet a hyperlinear-profile lower
bound. To obtain the latter one must control how defining-relator HS error
propagates through the balanced commutator words and then apply a robust
Heisenberg/Clifford dimension theorem. No dimension-independent error modulus
is claimed here.

## The three prefix costs

The exact dual-prefix construction has three different costs which must not
be conflated.

1. The coefficient address `t_u` or `s_u` has ring-word length `n`.
2. Sequential Steinberg multiplication gives the recurrence
   `L_seq(n)<=2L_seq(n-1)+C`, hence an exponential root-word upper bound.
   The balanced tree used above improves this to `L_bal(n)=O(n^2)`.
3. Transferring the complete depth-`n` multiplication table through an
   approximate representation costs the van Kampen areas of the equality
   words, not merely the lengths of their chosen representatives.  Those
   finite maxima are computable depth by depth as in
   `affine-leavitt-profile-computable-checkpoints`, but no bound uniform in
   `n` follows from `(LWR1)`.

In characteristic two, if the third cost were uniformly bounded, the
common-sign Pauli tower would meet
`uniform-bounded-area-clifford-tables-force-mark-collapse` and already prove
nonhyperlinearity.  Without it, the first two costs yield only the
computable growing-dimension checkpoints; hyperlinearity permits the matrix
dimension to grow.  This is the exact prefix-cost dichotomy relevant to the
dual-prefix route.
