---
rg: 2
id: stw30-matrix-corona-expander-centralization-proof
kind: route
title: Use a quantum-expander packet to keep every weak-divisibility block noncentral
target: stw30-quantum-expander-weak-divisibility-centralization-no-go
requires:
  - explicit-constant-degree-quantum-expanders
artifacts:
  - research/artifacts/stw30-quantum-expander-centralization-firewall-audit-2026-08-30.md
---

Choose the explicit quantum-expander family supplied by
`explicit-constant-degree-quantum-expanders`.  Thus `d_j->infinity`, the
number `D` of unitaries is fixed, and for normalized Hilbert--Schmidt norm
there is one `lambda<1` such that

```text
Phi_j(x)=(1/D) sum_(s=1)^D u_s^(j) x u_s^(j)*,
norm(Phi_j(x))_2 <= lambda norm(x)_2                    (3)
```

whenever `tr_(d_j)(x)=0`.  Let `Q` be the displayed norm matrix corona and
write `u_s=[(u_s^(j))]`.

## Real rank zero

The product `P=product_j M_(d_j)` has real rank zero directly.  Given a
bounded selfadjoint sequence and `epsilon>0`, move every eigenvalue in
`(-epsilon/2,epsilon/2)` to `epsilon/2`, coordinate by coordinate.  The
result is within `epsilon`, is selfadjoint, and has inverse norm at most
`2/epsilon` uniformly in `j`; it is therefore invertible in `P`.  The same
argument after taking a selfadjoint lift shows that invertible selfadjoints
are dense in the quotient `Q`.  Hence `rr(Q)=0`.

## Exact weak divisibility at every scale

Fix `n>=2`.  Every sufficiently large integer `d` has a representation

```text
d=na+(n+1)b,              a,b>=1.                       (4)
```

Indeed subtract `2n+1` and use the Frobenius conductor `n(n-1)` for the
coprime pair `n,n+1`.  For all sufficiently large `j`, equation `(4)` gives
the block representation

```text
M_n direct_sum M_(n+1) -> M_(d_j),
x direct_sum y |-> (x tensor 1_(a_j)) direct_sum
                       (y tensor 1_(b_j)).               (5)
```

Use zero maps in the finitely many omitted coordinates.  The product of
the tail maps descends to a unital injective star-homomorphism into `Q`:
the missing initial units are a finitely supported, hence `c_0`, sequence.

## The fixed packet excludes central blocks

Put

```text
F=M_2 direct_sum M_3,
h=e_11^(2) direct_sum e_11^(3).
```

Every unital representation `theta:F->M_d` has multiplicities `a,b>=0`
with `2a+3b=d`, not both zero.  Thus `q=theta(h)` is a projection and

```text
t=tr_d(q)=(a+b)/(2a+3b) in [1/3,1/2].                  (6)
```

For `y=q-t1`, equation `(3)` and the triangle inequality give

```text
(1-lambda) norm(y)_2
 <= norm(y-Phi_j(y))_2
 =  norm(q-Phi_j(q))_2
 <= max_s norm([q,u_s^(j)])_2
 <= max_s norm([q,u_s^(j)]).                            (7)
```

Since `q` is a projection, `(6)` gives

```text
norm(y)_2=sqrt(t(1-t)) >= sqrt(2)/3.
```

Therefore `(2)` holds with

```text
c=(1-lambda)sqrt(2)/3>0.                               (8)
```

Suppose now that a unital map as in `(1)` existed.  Finite-dimensional
C-star algebras are semiprojective.  Apply this to the increasing ideals of
sequences supported in the first `N` coordinates, whose union is dense in
the `c_0` ideal.  After discarding finitely many coordinates, the map has
star-homomorphic coordinate lifts

```text
theta_j:F->M_(d_j).
```

Their unit projections converge in norm to `1`; a projection at distance
less than one from `1` equals `1`, so the lifts are unital on a further
tail.  Commutation with every `u_s` in the `c_0` corona says

```text
max_s norm([theta_j(h),u_s^(j)]) -> 0,
```

contradicting `(8)`.

The countermodel is deliberately outside the hypotheses of Problem XXX:
`Q` is nonseparable and not simple, and no nuclearity assertion is made.
It therefore does not refute the Perera--Rordam question.  It proves the
sharp methodological point that real rank zero plus the entire family of
exact weak-divisibility embeddings cannot by itself supply centrality, even
against one fixed finite unitary packet.  At least one additional structural
or uniform-selection input is necessary; this example does not distinguish
which of separability, simplicity, nuclearity, or another input supplies it.
