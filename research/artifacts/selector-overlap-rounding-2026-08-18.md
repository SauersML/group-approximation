# 2026-08-18 — Pairwise selector overlap is the only nonlinear mass in predicated ZPC compilation

**Status:** two elementary operator lemmas are proved below.  No nonhyperlinear
group is claimed here.  The consequence is a substantial narrowing of the
perfect-ZPC-to-LCS route: once a compiler makes pairwise selector overlap pay
for LCS relator energy, one-hot rounding and branchwise decoding are automatic
with dimension-free constants.

This note complements the existing affine and finite-group selector no-gos.
Those results say one-hot selector semantics cannot be imposed exactly by a
standalone finite group gadget.  The statements here go in the other direction:
they show that **exact one-hot semantics is unnecessary**.  Quantitative
suppression of pairwise overlap is enough.

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

and for `h=0` both sides vanish.  This proves (O2).

The important feature is what is absent: there is no factor depending on
matrix dimension.

## 2. Direct-sum predication decoder

The existing `controlled-linear-predication-normal-form` introduces a gated
copy `G_(a,i)` of an unreadable involution for every branch `a` and variable
`i`.  A previous formulation also linked all gated copies back to one common
operator.  That link is not needed for sound decoding.

Assume the selector family above and suppose every `G_(a,i)` is a
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

On `Q_a`, exactly one selector is hot, so

```text
Q_a Z_a^b = (-1)^b Q_a.
```

Moreover

```text
Q_a product_(i in I) U_i = Q_a H_(a,I).
```

Therefore

```text
||Q_a (product_(i in I) U_i - (-1)^b)||_2
    <= ||H_(a,I)-Z_a^b||_2.                        (D2)
```

After normalizing the trace on the good corner, the squared defect is enlarged
by at most the factor `1/tau(Q)`.  Hence if

```text
r := (1/4)||W+1||_2^2 + S < 1,
```

then `tau(Q)>=1-r`, and every weighted sum of branch-equation squared defects
for the decoded controlled-linear strategy is at most

```text
(compiled weighted squared defect)/(1-r).           (D3)
```

Crucially, the decoder does **not** need relations of the form
`product_a G_(a,i)=U_i`, nor does it need inactive gated copies to equal one.
It simply uses the correct gated copy on each selector sector and takes their
direct sum.

## 3. Consequence for the ZPC compiler

For the fixed separated game supplied by `perfect-zpc-irs-quantum-gap-game`,
all the following are already available in Cairn:

1. perfect ZPC-IRS completeness and source quantum value `<1/2`;
2. exact lowering of every controlled-linear branch relation to a predicated
   parity relation (`controlled-linear-predication-normal-form`);
3. exact compilation of finite affine equations plus prescribed commutations
   into LCS syntax (`finite-linear-commutation-system-to-lcs`).

The two lemmas above show that the remaining nonlinear task can be stated as
one quantitative inequality:

> build a payload-coupled LCS selector system for which the odd-parity defect
> and the total pairwise overlap
> `sum_(a<b) tau(P_a P_b)` are bounded by a universal constant times the total
> output relator/game loss.

If that holds, near-perfect output strategies have `tau(Q)->1`; (D3) decodes
them to source strategies with value tending to one, contradicting the fixed
source bound `<1/2`.  Thus this **pairwise-overlap transducer** is sufficient
for the robust compiler and hence for an explicit nonhyperlinear solution
group.

This target is strictly weaker than enforcing one-hot exactly.  It is also
compatible with the new extensive-syndrome accounting lane: pairwise overlap
mass is a positive spectral carrier, and a successful local transducer only
has to make that carrier pay bounded-overlap relator energy.

## 4. What this rules out and what it opens

The affine and finite-group induction barriers remain valid.  A successful
transducer cannot be a standalone finite selector gadget whose only visible
boundary is the commuting selector subgroup.  It must couple invalid overlap
sectors to the payload or to an infinite/stable syndrome mechanism.

But the compiler no longer owes a representation-theoretic classification of
all selector sectors.  It owes one dimension-free energy inequality.  That is
a substantially smaller target, and it can be attacked using stability,
local-testability, spectral-carrier, or code-syndrome methods without changing
the downstream LCS/nonhyperlinear argument.
