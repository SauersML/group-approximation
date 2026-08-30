---
rg: 2
id: local-multiplier-host-destabilization-proof
kind: route
title: Build and destabilize the finite packet entirely inside a local multiplier host
target: local-multiplier-hosts-solve-lxxiii
requires:
  - finite-square-zero-packet-covers-cutdown
  - finite-packets-fuse-after-one-stabilization
---

If `c=0`, then `(a-epsilon)_+=0` and `x=0` works.  Assume `c!=0`.

First observe that `B` has no nonzero finite-dimensional representation.
Indeed, after compressing such a representation to its support, it is
nondegenerate and extends unitally to `M(B)`.  A multiplier Cuntz pair would
then map to two isometries with orthogonal ranges in a nonzero
finite-dimensional corner, which is impossible.

Apply the finite-packet theorem inside `B`, with positive element `c` and
tolerance `epsilon/2`.  It gives square-zero elements `x_1,...,x_n in B`
such that

```text
h=(c-epsilon/2)_+=(a-epsilon)_+
  in I=Ideal_B(x_1)+...+Ideal_B(x_n).                (1)
```

The one-stabilization theorem gives `W in M_2(B)` with

```text
W^2=0,
h tensor e_11 in Ideal_(M_2(B))(W).                  (2)
```

Proper infiniteness of `1_(M(B))` supplies isometries `s_1,s_2 in M(B)`
with

```text
s_i^*s_j=delta_(i,j)1.
```

They define an injective star homomorphism

```text
Theta:M_2(B)->B,
Theta((b_ij))=sum_(i,j=1)^2 s_i b_ij s_j^*.
```

Set `x=Theta(W)`.  Then `x^2=0`, and (2) gives

```text
s_1 h s_1^*=Theta(h tensor e_11) in Ideal_B(x)=J.
```

Every closed ideal of `B` is invariant under multiplication by `M(B)`.
Multiplication by `s_1^*` and `s_1` therefore recovers

```text
h=s_1^*(s_1 h s_1^*)s_1 in J.
```

Since `J subset Ideal_A(x)`, this proves the local assertion.  Applying it
to a host for `(a-epsilon/2)_+` proves the global criterion.  If `A` is a
counterexample, the negation of that criterion gives the asserted unhosted
cutdown; its hereditary subalgebra and generated ideal are two particular
subalgebras containing it.

The enlargement over the global multiplier result is genuine.  Let

```text
D=C_0((0,1]) tensor K,             A=unitization(D).
```

The algebra `D` is both stable and projectionless.  Stability makes
`1_(M(D))` properly infinite.  On the other hand `1_A` is finite: if
`v in A` is an isometry,
its scalar quotient has modulus one, and the defect projection
`1-vv*` lies in the projectionless ideal `D`; hence the defect is zero and
`v` is unitary.  Every cutdown supported in `D` can nevertheless use `D` as
its local host.  Thus local destabilization applies to nonzero cutdowns in
an ambient algebra with finite multiplier unit.  (This unitization has a
one-dimensional quotient, so it illustrates strictness of the local theorem,
not a new global LXXIII class.)
