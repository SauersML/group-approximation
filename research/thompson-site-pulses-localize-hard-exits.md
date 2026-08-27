---
rg: 2
id: thompson-site-pulses-localize-hard-exits
kind: claim
title: Thompson site pulses localize every hard exit in a fresh first-hit sector
distinct_from:
  commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir: that proves the abstract prefix telescope and leaves prefix preservation as an analytic obligation; this constructs a finitely presented site geometry in which the local hard transporter preserves every earlier pulse.
  e5-tail-character-suppression-for-projected-exits: that tries to suppress persistent characters of overlapping polynomial E5 pulses; this replaces those pulses by independent Thompson-site signs, so no character tail can revisit an earlier site.
  thompson-clifford-central-product-tape: that places one Pauli pair at every site with a common sign; this places a doubled arbitrary finite packet and its hard-sign swap at every site to obtain an oriented first-hit transporter.
---

Let `H` be a fixed finite group with central involution `J`, let `a in H` be
an involution, and suppose `H` has a unitary representation with `J=-I`.
Form the finite group

```text
L=((H times H)/<(J,1)=(1,J)>) semidirect <s>,            (TSP1)
```

where `s` swaps the two factors.  In `L` put

```text
A=(a,1),             B=(1,a),             sAs^-1=B.     (TSP2)
```

Let Thompson `V` act on its rational tail orbit `X`, put one copy `L_x` at
each site, central-product all local signs, and form

```text
Gamma_(H,a)=((centralProduct_X L_x) semidirect V).       (TSP3)
```

Then `Gamma_(H,a)` is finitely presented and its common `J` is nontrivial.
Choose distinct sites `x_0,x_1,...` with address length `O(n)`, and write
`A_n,B_n,s_n` for the three words at `x_n`.  The `B_n` are commuting
involutions and

```text
s_n A_n s_n^-1=B_n,        [s_n,B_k]=1 for k!=n.         (TSP4)
```

In any exact unitary representation define

```text
C_n=product_(k<n)(I+B_k)/2,
X_n=C_n(I-B_n)/2.                                      (TSP5)
```

If a projection `P_n` satisfies

```text
P_n<=C_n,                     A_n P_n=-P_n,             (TSP6)
```

then

```text
s_n P_n s_n^*<=X_n.                                    (TSP7)
```

The `X_n` are pairwise orthogonal and `sum_(n<N)tau(X_n)<=1`.

There is also a polynomial approximate form.  At every fixed depth `N`,
exactify the finite elementary abelian pulse table and align it with the
fixed local packet tables.  If `E` is the total named squared relator energy,
the corrected projections and transporters satisfy

```text
||(I-X_n)s_nP_n||_2^2<=p(n)E                           (TSP8)
```

for one polynomial `p` independent of ambient matrix dimension.  Thus this
site-pulse geometry supplies precisely the prefix-leakage estimate needed by
the first-hit ledger, without a coefficient-valuation or tail-suppression
theorem.
