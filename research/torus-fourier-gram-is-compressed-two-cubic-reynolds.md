---
rg: 2
id: torus-fourier-gram-is-compressed-two-cubic-reynolds
kind: claim
title: Every torus-character Gram block is a compression of two cubic Reynolds projections
distinct_from:
  right-u-reynolds-has-torus-hecke-blocks: that gives the weighted Mobius matrices for the two column rows; this computes their normal operator and the exact Fourier correlation formula.
  proper-torus-reynolds-is-edge-refinement: that gives the global labeled-edge geometry and missing triangle lifts; this identifies the positive compressed-Hecke operator on each label character.
  near-trivial-torus-characters-track-the-moving-kernel: that rules out a perturbative singular-value mechanism near one character; this proves that orthogonality of all characters supplies only an average Parseval identity, not characterwise diagonal dominance.
---

Use the prime-field notation of
`right-u-reynolds-has-torus-hecke-blocks`.  On `l2(G)` put

```text
Q=P_(N,chi) P_U,
P_(N,chi)=|N|^(-1) sum_(n in N) conjugate(chi(n)) L_n,
P_U=|U|^(-1) sum_(u in U) R_u.                         (TFG1)
```

The two projections commute.  The scalar domain is `W=ran(Q)`.  Right
translation by the split torus commutes with `Q`; for `theta in dual(T)` let

```text
W_theta=ran(QP_theta).
```

Write

```text
a=S^2 A S^(-2),       b=S B S^(-1),
P_a=(I+L_a+L_(a^2))/3,
P_b=(I+L_b+L_(b^2))/3.                                (TFG2)
```

Then the exact normal operator of the `theta` column is

```text
C_(G,theta)^* C_(G,theta)
 =9 (QP_theta)(P_a+P_b)(QP_theta)|_(W_theta).           (TFG3)
```

In particular it is a sum of two positive compressed Reynolds projections,
and

```text
ker C_(G,theta)
 =W_theta cap ker(P_a) cap ker(P_b).                   (TFG4)
```

Thus the Hilbert singular-value question is exactly the lower-frame problem

```text
||P_a f||_2^2+||P_b f||_2^2 >= gamma ||f||_2^2
       (f in W_theta cap ker(C_(G,theta))^perp),        (TFG5)
```

while the required infinity Green estimate is a strictly stronger
unconditional-basis statement.

## Proof of the normal formula

Set `R_A=I+L_A+L_(A^2)` and similarly for `B`.  The unrestricted row
operators in `(DSS3)` are

```text
T_1=R_A L_(S^(-2)),       T_2=R_B L_(S^(-1)).
```

Since `A^3=B^3=1`,

```text
R_A^*=R_A,   R_A^2=3R_A,
R_B^*=R_B,   R_B^2=3R_B.                              (TFG6)
```

Consequently

```text
T_1^*T_1=3(I+L_a+L_(a^2))=9P_a,
T_2^*T_2=3(I+L_b+L_(b^2))=9P_b.                       (TFG7)
```

The adjoint of the restriction `T_i|_W` is `Q T_i^*`, so its normal
operator is the compression `Q T_i^*T_i Q`.  Right translations commute
with every left translation and with `Q`; inserting `P_theta` gives
`(TFG3)`.  Positivity gives `(TFG4)` and `(TFG5)`.

The two outside copies of `Q` in `(TFG3)` are load-bearing.  The left
translations `L_a,L_b` need not preserve the signed induced domain
individually, so dropping the compression produces the wrong Cayley-graph
normal operator.

## Exact Fourier correlation formula

Choose an orthonormal signed-coset basis `(e_x)` of `W`.  On a free right
`T`-orbit `O_x`, use

```text
xi_(x,theta)=|T|^(-1/2) sum_(t in T)
              conjugate(theta(t)) R_t e_x.             (TFG8)
```

For `g in G` define its orbit-correlation sequence

```text
k_(g;x,y)(r)=<e_x, Q L_g Q R_r e_y>.                   (TFG9)
```

Left and right translations commute, so direct expansion of `(TFG8)` gives

```text
<xi_(x,theta), QL_gQ xi_(y,theta)>
 =sum_(r in T) theta(r) k_(g;x,y)(r).                  (TFG10)
```

(The choice of `theta` versus its conjugate depends only on the convention
in `(TFG8)`.)  Therefore every entry of the Gram matrix `(TFG3)` is the
Fourier transform of the sum of the six correlation sequences belonging to

```text
g in {1,a,a^2,1,b,b^2}.                               (TFG11)
```

For nonfree orbits the identical formula holds on `T/T_x` for precisely the
characters trivial on the stabilizer, as in `(RUB5)`.

## Orthogonality firewall

On a free orbit pair, Parseval applied to `(TFG10)` says

```text
sum_(theta in dual(T))
 |<xi_(x,theta),QL_gQ xi_(y,theta)>|^2
 =|T| sum_(r in T)|k_(g;x,y)(r)|^2.                   (TFG12)
```

Thus torus orthogonality **redistributes** the raw overlap energy among the
characters; it does not bound every Fourier coefficient.  In particular,
a correlation supported at one label has the same absolute Fourier
coefficient for every character.  Character phases then give no diagonal
dominance improvement at all.  Only an arithmetic statement about the
actual correlation sequences -- cancellation of every Fourier coefficient,
or a characterwise routing estimate for the compressed operator -- can
prove a uniform bound.

This is not a divergent block and does not settle the proper-subtorus gate.
It narrows it to a concrete finite harmonic-analysis question: uniformly in
`p,theta`, control the Moore--Penrose Green operator of the positive Hecke
compression `(TFG3)`.  Mere orthogonality of distinct `theta` blocks, or an
average estimate obtained from `(TFG12)`, is insufficient for the required
supremum over characters and for Fourier recombination in `l_infinity`.

