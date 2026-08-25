---
rg: 2
id: positive-tree-choi-gap-does-not-force-ideal-support
kind: claim
title: A positive tree Choi gap can live entirely in the augmentation block
distinct_from:
  positive-tree-separator-has-fd-low-ideal-moment-packets: that approximates the positive quotient Choi state by finite-dimensional packets with correlated low ideal moments and leaves trivial-summand leakage open; this gives an exact scalar Choi state showing that the leakage can carry a fixed positive tree-defect value.
  km-triangle-relative-gap-failure-has-fd-full-support-witnesses: that constructs other low-relator packets from failure of relative property T and removes their trivial summands using a separately chosen kernel displacement; this proves that the positive tree defect used here does not itself permit that removal.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that algebraically splits a given finite packet into its ideal and scalar quotient blocks; this shows that the positive quotient witness can be supported wholly on the scalar block before any packet repair is considered.
---

**ESTABLISHED (augmentation leakage firewall).**  Let `H` be either tree
face `P_12` or `P_23`, and put

```text
L=H intersect P_13,
D_H=(id-M_(P_13))|_(C^*(H))=id-M_L.                         (ATF1)
```

Here `L=P_1` for `H=P_12` and `L=P_3` for `H=P_23`; in either case `L` is a
proper subgroup of the finite group `H`.  Let

```text
p_H=|H|^(-1) sum_(h in H)u_h
```

be the central projection of the trivial `H`-representation.  Under the
finite-dimensional Choi decomposition of `C^*(H)`, the source block
`C p_H` is a one-dimensional matrix block.  Evaluate that Choi block by the
augmentation character `epsilon:Q->C`.  This defines a positive Choi state
`Omega_aug`, and

```text
Omega_aug(C_(D_H))
 =epsilon(D_H(p_H))
 =1-|L|/|H|
 =1-[H:L]^(-1)>0.                                         (ATF2)
```

Nevertheless its pullback through the amplified quotient
`C^*(G_0)->>Q` is exactly the one-dimensional trivial representation of
`G_0`.  It annihilates the entire relator ideal, and its ideal support
projection is zero.  Thus a fixed positive Choi value on the canonical tree
defect does not imply any positive ideal-block mass.

There is also no universal augmentation-centering rescue.  Let

```text
E_epsilon(x)=epsilon(x)1,
D_H^0=(id-E_epsilon) o D_H.                                (ATF3)
```

Then `D_H^0` is unital-zero and augmentation-zero, but

```text
Omega_aug(C_(D_H^0))=0                                    (ATF4)
```

while `(ATF2)` stays uniformly positive.  Therefore no lower bound for an
augmentation-zero replacement can be deduced from positivity and the
original tree-defect value alone.  Freedom in the bounded face splitting or
in adding a unit-evaluation functional during Choi positivization does not
alter this conclusion: unit-evaluation functionals vanish on `D_H`, whereas
`(ATF2)` is already carried by the augmentation of the output.

**Consequence.**  To force the correlated finite-dimensional packets into
the ideal block, one needs an additional separator estimate after quotienting
the tree Choi dual by all augmentation-supported functionals (or a second
observable vanishing in the trivial representation).  Positive Choi duality
and low ideal moments alone cannot supply it.

Proof: `evaluate-the-tree-fourier-defect-on-the-trivial-source-block`.

DERIVATION
evaluate-the-tree-fourier-defect-on-the-trivial-source-block
