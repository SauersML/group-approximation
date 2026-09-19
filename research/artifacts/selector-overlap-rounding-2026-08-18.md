# 2026-08-18 — Pairwise selector overlap quantitatively rounds predicated control

**Status:** two elementary operator lemmas are proved below.  No nonhyperlinear
group is claimed here.  They substantially narrow one part of the
perfect-ZPC-to-LCS route: within any common selector context, pairwise selector
overlap is the only obstruction to a large one-hot corner, and branch-specific
gated copies decode there by direct sum with dimension-free constants.

This note complements the existing affine and finite-group selector no-gos.
Those results say one-hot selector semantics cannot be imposed exactly by a
standalone finite group gadget.  The statements here go in the other direction:
they show that **exact one-hot semantics is unnecessary** once an output
construction has supplied a common selector context and quantitative overlap
control.

## 1. Selector overlap rounding

Let `(M,tau)` be a finite tracial von Neumann algebra (matrices are the intended
application).  Let

```text
Z_1,...,Z_m
```

be commuting self-adjoint involutions and put

```text
P_a = (1-Z_a)/2,
W   = product_a Z_a.
```

Thus the `P_a` are commuting projections.  Define the exactly-one projections

```text
Q_a = P_a product_(b != a) (1-P_b),
Q   = sum_a Q_a,
S   = sum_(a<b) tau(P_a P_b).
```

The `Q_a` are pairwise orthogonal.  Then

```text
tau(1-Q) <= (1/4)||W+1||_2^2 + S,                 (O1)
sum_a ||P_a-Q_a||_2^2 <= 2 S.                    (O2)
```

If the odd-parity relation is exact, `W=-1`, the first bound sharpens to

```text
tau(1-Q) <= S/3.                                  (O3)
```

### Proof

Use the joint spectral decomposition of the commuting projections.  A joint
atom is indexed by a bit vector `s in {0,1}^m`; write

```text
h = sum_a s_a.
```

On that atom, `Q=1` exactly when `h=1`, while

```text
sum_(a<b) P_a P_b = binom(h,2).
```

Also `W=(-1)^h`, so

```text
(1/4)|W+1|^2 = 1_(h even).
```

Pointwise,

```text
1_(h != 1) <= 1_(h even) + binom(h,2),
```

which integrates to (O1).  If `W=-1`, only odd `h` occur.  Every bad atom then
has `h>=3`, hence `binom(h,2)>=3`, proving (O3).

Since `Q_a<=P_a`,

```text
||P_a-Q_a||_2^2 = tau(P_a-Q_a).
```

Summing over `a`, the joint-atom contribution is `h` when `h!=1` and zero when
`h=1`.  For every `h>=2`,

```text
h <= 2 binom(h,2),
```

and for `h=0` both sides vanish.  This proves (O2).  There is no matrix-dimension
factor.

## 2. Direct-sum predication decoder

Assume the selector family above and suppose every branch copy `G_(a,i)` is a
self-adjoint involution commuting with every selector `Z_b`.  On the good
corner `Q M Q`, define

```text
U_i = sum_a Q_a G_(a,i).
```

Because the `Q_a` are an orthogonal partition of `Q` and commute with the
`G_(a,i)`, each `U_i` is a self-adjoint involution in the corner.

For branch `a`, let a selected affine equation be

```text
sum_(i in I) x_i = b mod 2,
```

and suppose the compiled predicated relation is

```text
H_(a,I) := product_(i in I) G_(a,i) ~= Z_a^b.      (D1)
```

On `Q_a`, exactly one selector is hot, so `Q_a Z_a^b=(-1)^b Q_a`, and

```text
Q_a product_(i in I) U_i = Q_a H_(a,I).
```

Therefore

```text
||Q_a (product_(i in I) U_i - (-1)^b)||_2
    <= ||H_(a,I)-Z_a^b||_2.                        (D2)
```

After normalizing the trace on the good corner, squared defects enlarge by at
most `1/tau(Q)`.  Hence if

```text
r := (1/4)||W+1||_2^2 + S < 1,
```

then `tau(Q)>=1-r`, and a weighted sum of decoded branch-equation squared
defects is bounded by the corresponding compiled sum divided by `1-r`.

No relation `product_a G_(a,i)=U_i`, and no requirement that inactive gated
copies equal one, is needed **inside this common selector context**.

## 3. The remaining ZPC issue: contexts have to glue

For a generic TailoredMIP ZPC strategy, unreadable operators at a question are
known to commute with readable operators at that question and across incident
edges, not with every remote readable bit.  Consequently the natural
predication contexts are local (typically one edge and its two readable
answers), not one global readable assignment.  Applying Sections 1–2
independently on every edge can therefore produce different decoded copies of
the same unreadable question variable on different incident edges.

That is a genuine remaining soundness condition.  The two lemmas here do **not**
prove `zpc-selector-robust-lcs-compiler` on their own.  They split its analytic
burden into two explicit quantities:

1. **selector overlap energy** in each local context, measured by
   `sum_(a<b) tau(P_a P_b)` plus the odd-parity defect; and
2. **context consistency energy**, measuring the mismatch between decoded
   copies of the same question observable across its incident edge contexts.

Once both are bounded by a dimension-free constant times output LCS loss, a
finite spanning-tree gluing argument chooses one reference context per question,
transports all edge equations to those references, and yields a legitimate
source strategy with loss tending to zero.

This is still a major simplification: the compiler need not classify selector
representations or enforce exact one-hot.  It needs two positive energy
inequalities that are local and quantitative.

## 4. Why the overlap quantity is a promising syndrome target

The affine and finite-group induction barriers remain valid.  A successful
mechanism cannot be a standalone finite selector gadget whose only visible
boundary is the commuting selector subgroup.  It must couple invalid overlap
sectors to payload/context relations or to an infinite/stable syndrome
mechanism.

Pairwise overlap mass is nevertheless a particularly tractable target: it is a
sum of traces of positive spectral carriers.  The repository's new
bounded-overlap syndrome accounting shows exactly how positive carrier density
can be charged to a finite relator-energy budget once a local transducer is
available.  The next theorem should therefore be sought as a
**context-coupled overlap/mismatch transducer**, not as another exact selector
presentation.
