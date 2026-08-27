---
rg: 2
id: product-clock-synchronizes-fanizza-and-e5
kind: claim
title: A commuting product clock synchronizes Fanizza levels with the one-sided E5 boundary
distinct_from:
  fanizza-symmetric-kernel-has-two-root-e5-clock: that constructs the E5 transporter and its degree profile; this synchronizes its iterate with the Turing recurrence without identifying the two shift words.
  fanizza-boone-mark-carrier-interface: that must feed a separated word into the initial carrier; this aligns all later packet and boundary levels after an initial carrier has been supplied.
---

Take commuting Fanizza and E5 factors with shift words `U` and `D_L`, and put

```text
T=U D_L.                                                (PCL1)
```

For one atom-aligned paired frame, let `s_0,...,s_3` be its source words and
`c_0,...,c_3` its coefficient words.  Impose only the finite cross relations

```text
[D_L,s_i]=1,   [U,c_i]=[D_L,c_i]=1,   [U,D_L]=1,        (PCL2)
```

and let `w_i=s_i c_i`.  If `b` is the aligned E5 hard root, impose the single
base bridge

```text
[w_0,w_2]=b.                                            (PCL3)
```

Then for every `n>=0`, conjugating `(PCL3)` by the one word `T^n` gives

```text
[ (U^n s_0 U^-n)c_0, (U^n s_2 U^-n)c_2 ]
   = D_L^n b D_L^-n.                                   (PCL4)
```

Thus the source half of the finite frame advances through exactly the same
`U^n` levels as the Fanizza projections, the coefficient half remains fixed,
and its hard sign lands on exactly the degree-`2n` E5 boundary pulse.  No
infinite family of relators is added: `(PCL4)` is a conjugate of one base
relator, and the word/derivation cost through level `n` is polynomial (in fact
linear before expanding the fixed Fanizza and E5 normal forms).

Crucially, `(PCL1)` does **not** impose `U=D_L`.  In a satisfying exact tracial
model, choose the coefficient packet's diagonal character so that the
unsheared combined frame is abelian, map the E5 factor and `D_L` trivially,
and retain the published Fanizza representation of `U`.  Then both sides of
`(PCL3)` are the identity and `T` acts as `U`.  Hence this synchronization
step by itself preserves the known exact model.

For approximate representations, `(PCL4)` is precisely the hard-sign
intertwining word consumed by `hard-sign-transport-captures-exit-mass`.
Together with the first-detection Fourier theorem, the same integer `n` now
labels the Turing carrier, the one-sided symmetric frame, and the summable E5
exit layer.
