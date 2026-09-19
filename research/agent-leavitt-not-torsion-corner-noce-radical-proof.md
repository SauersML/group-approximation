---
rg: 2
id: agent-leavitt-not-torsion-corner-noce-radical-proof
kind: route
title: Normalize the surviving torsion spectral corner by its intrinsic matrix rank
target: agent-leavitt-not-torsion-corner-noce-forces-mf-radical
requires: []
---

Let

```text
Q=(product_n M_(d_n)(C))/(directSum_(||.||) M_(d_n)(C))
```

and let `theta:G -> U(Q)` be any homomorphism.  Its linear extension is a
unital star homomorphism `C[G] -> Q`.  Write `u=theta(z)` and

```text
p=theta(q_z)=1-(1/m)sum_(j=0)^(m-1)u^j.                     (TCN4)
```

Because `u^m=1`, functional calculus identifies `1-p` with the spectral
projection of `u` at `1`.  Consequently

```text
p=0  iff  u=1.                                               (TCN5)
```

Suppose for contradiction that `theta(z)!=1`.  Then `p` is a nonzero
projection.  A projection in the norm matrix corona lifts to a sequence of
projections: take a self-adjoint lift whose idempotence defect tends to zero
and apply the spectral cut at `1/2`.  Thus, after passing to an infinite
subsequence on which the lifts are nonzero, write

```text
p=[(p_n)],              p_n in M_(d_n),
r_n=rank(p_n)>0.                                           (TCN6)
```

There is a canonical unital star homomorphism

```text
pQp
 -> product_omega (p_n M_(d_n)p_n,tr_(r_n))                 (TCN7)
```

for any free ultrafilter on this subsequence.  Indeed, represent an element
of `pQp` by `(p_n a_n p_n)` and then quotient by the normalized
Hilbert--Schmidt null ideal.  This is well defined because norm-null sequences
are normalized-Hilbert--Schmidt-null.  Under the identifications
`p_n M_(d_n)p_n ~= M_(r_n)`, the image of `p` is the unit.  Notice that no
lower bound on `r_n/d_n` is used.

Now compose

```text
B --Phi--> q_z C[G]q_z --theta--> pQp --(TCN7)-->
product_omega (M_(r_n),tr_(r_n)).                           (TCN8)
```

The composition is unital.  Pulling back the ultraproduct trace gives a
Connes-embeddable tracial state on `B`, contradicting the hypothesis.
Therefore `theta(z)=1`.  Since `theta` was arbitrary, `z in Rad_MF(G)`.

If the normal closure of `z` is all of `G`, every such `theta` kills all of
`G`, so `Rad_MF(G)=G`.  End proof.

