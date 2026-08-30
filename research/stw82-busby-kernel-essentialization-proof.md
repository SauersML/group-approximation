---
rg: 2
id: stw82-busby-kernel-essentialization-proof
kind: route
title: Absorb the Busby kernel to make the ideal essential
target: stw82-every-counterexample-essentializes
requires: []
---

Write `q_I : M(I) -> Q(I)` for the corona quotient.  Multiplication on `I`
gives a canonical *-homomorphism `sigma : E -> M(I)`.  The Busby map is

```text
tau(pi(e))=q_I(sigma(e)).
```

The standard pullback model is particularly transparent here:

```text
P_tau = {(m,d) in M(I) directSum D : q_I(m)=tau(d)}.
```

For the standard pullback description and the criterion that an extension is
essential exactly when its Busby map is injective, see Section 2.2 of
[Evington--Ng--Sims--White](https://arxiv.org/abs/2409.12872).

The map `e |-> (sigma(e),pi(e))` is an isomorphism from `E` onto `P_tau`.
Indeed, if both coordinates vanish, then `e` belongs to `I` and annihilates
`I`; an approximate identity for `I` gives `e=0`.  Conversely, if `(m,d)`
lies in the pullback and `e` is any lift of `d`, then
`m-sigma(e)` belongs to `I`, so adding that element of `I` to `e` produces
the prescribed pair.

Let `K=ker(tau)`.  In the pullback picture,

```text
L=pi^(-1)(K)
 ={(m,k): k in K and q_I(m)=0}
 =I directSum K.                                      (1)
```

Also `E/L` is canonically `D/K`.  It remains to prove that `L` is essential.
Suppose `(m,d)` annihilates `L` on both sides.  Since `I directSum 0` is
contained in `L`, the multiplier `m` annihilates `I`; the multiplier action
is faithful, hence `m=0`.  The pullback equation now gives `tau(d)=0`, so
`d` belongs to `K`.  Thus `(0,d)` belongs to `L`.  Its annihilation of
`0 directSum K`, followed by an approximate identity for `K`, gives `d=0`.
The two-sided annihilator of `L` is therefore zero, which is exactly
essentiality.

Nuclear dimension is the maximum on a finite direct sum and does not
increase on quotients.  Equation (1) consequently gives

```text
dim_nuc(L)=max(dim_nuc(I),dim_nuc(K))
          <=max(dim_nuc(I),dim_nuc(D)),
dim_nuc(D/K)<=dim_nuc(D).                            (2)
```

Now suppose the original extension is a counterexample and put
`n=max(dim_nuc(I),dim_nuc(D))`.  The number `n` is finite, since an infinite
endpoint already forces `dim_nuc(E)=infinity` by monotonicity.  We have
`dim_nuc(E)>n`, while (2) bounds both endpoints of the essential extension
by `n`.  Hence that extension is again a counterexample.  The reverse
reduction is tautological because an essential extension is an extension.

Finally, if `E` is separable, then its ideals and quotients `I`, `D`, `K`,
`L`, and `D/K` are separable.  Applying this construction after the existing
separable-reflection theorem proves the last assertion.
