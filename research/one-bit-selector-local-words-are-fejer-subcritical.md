---
rg: 2
id: one-bit-selector-local-words-are-fejer-subcritical
kind: claim
title: Every local one-bit selector word stays below the canonical Fejer threshold
distinct_from:
  one-bit-clifford-selector-halves-a-chosen-bcs-atom: that proves the selected half has the right nonlinear mass; this proves that no word in the same local selector packet can turn that mass into a terminal fixed carrier.
  finite-selector-cannot-support-infinite-child-fixedness: that rules out pointwise fixedness by an infinite self-copy child; this also rules out the weaker one-word unnamed-carrier terminal inside the complete local selector subgroup.
  finite-clock-fejer-threshold-is-sharp: that gives the abstract finite-clock ceiling; this identifies the exact order-two/order-four clocks arising from the nonlinear selector normal form and compares them with one context atom.
---

Fix a nonempty BCS context `c`, an assignment `a`, and the one-bit selector
packet

```text
[p,q]=r=J^(1-a(v_0))x_(v_0),
p^2=q^2=J^2=x_v^2=1,
[p,J]=[q,J]=[p,x_v]=[q,x_v]=1       (v in c).         (SLF1)
```

Let

```text
H=<J,x_v:v in c>,
E=Q_- P_(c,a),                 Q_-=(1-J)/2.            (SLF2)
```

Assume the context subgroup is embedded, as it must be in any use of the
canonical Reynolds atom.  Then every word in the local group

```text
L_(c,a)=<H,p,q>                                           (SLF3)
```

has, after compression to `E`, one of the four forms

```text
plus/minus 1,       plus/minus p,       plus/minus q,
plus/minus pq.                                           (SLF4)
```

The first form comes from an element of the elementary-abelian context
subgroup and therefore has order at most two.  The middle two have two
eigenspaces of equal `E`-trace.  The last has eigenvalues `plus/minus i`,
again with equal `E`-trace, and has order four.  Consequently no word in
`L_(c,a)` supplies the supercritical fixed carrier required by
`unnamed-positive-density-fixed-space-is-terminal`:

```text
order two:   fixed mass <= tau(E) <= 1/4 < 1/2,
order four:  one-phase mass <= tau(E)/2 <= 1/8 < 1/4.   (SLF5)
```

Here the canonical context trace is

```text
tau(E)=1/2^(|c|+1)<=1/4,                                (SLF6)
```

because `c` is nonempty.  The inequalities persist with `o(1)` error in
canonical normalized-HS microstates after the fixed context/selector packet
is exactified.

In particular, the visibly fixed selected half

```text
A=E(1+p)/2                                               (SLF7)
```

is fixed by the involution `p`, but its density is only `tau(E)/2`; the
factor two required by the order-two Fejer test is not merely unproved, it
is impossible inside this packet.  The phase-sensitive selector product
`pq` is no better: it is an order-four clock and each of its two phase
carriers again has density `tau(E)/2`.

Thus the nonlinear selector does solve atom selection, but its entire local
word algebra is terminally subcritical.  A surviving macroscopic amplifier
must introduce a genuinely nonlocal return word whose order or wandering
behavior is not already contained in `<H,p,q>`, and it must authenticate the
same selected carrier under that word.  Merely choosing a different local
selector word, multiplying by context signs, or passing from `p` to the raw
square root `pq` cannot do so.

DERIVATION
one-bit-selector-local-fejer-proof
