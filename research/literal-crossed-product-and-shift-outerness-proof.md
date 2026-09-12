---
rg: 2
id: literal-crossed-product-and-shift-outerness-proof
kind: route
title: Expose the expected nonamenable group factor and the outer block shift
target: literal-canonical-shift-model-stops-at-r-omega
requires:
  - literal-telescope-split-normal-form
---

The group `V` contains the displayed copy of `SL_3(Z)`, so `V` is
nonamenable.  In the canonical crossed product

```text
M=A crossed_product_beta V
```

the group unitaries generate `L(V)`.  Trace preservation makes the formula

```text
E_V(sum_g a_g u_g)=sum_g tau(a_g) u_g
```

a faithful normal conditional expectation from `M` onto `L(V)`.  If `M`
were hyperfinite, it would be injective; injectivity passes through a normal
conditional expectation, so `L(V)` would be injective.  For a discrete
group this is equivalent to amenability of `V`, a contradiction.  Hence the
canonical crossed product is not hyperfinite.  Its canonical character
restricts on `V` to the regular character, which is precisely the forbidden
nonamenable summand.

The same obstruction is intrinsic at the character level.  If a character
`chi` of `E` had hyperfinite GNS algebra `M_chi` and `chi|V` were regular,
then

```text
pi_chi(V)'' ~= L(V).
```

Every von Neumann subalgebra of a finite von Neumann algebra is the range of
the trace-preserving normal conditional expectation.  Thus `L(V)` would be
an expected subalgebra of the hyperfinite, hence injective, algebra `M_chi`.
It would be injective, contradicting nonamenability of `V`.  This rules out
any central-mark sector which leaves the quotient character regular, not
only a literal crossed-product realization.

It remains to make the honest-factor/ultrapower gap explicit.  Let
`A_0=bar_tensor_Z F`, with `F=M_d(C)`, `d>=2`, and let `sigma` shift tensor
coordinates by one.  Suppose `sigma=Ad(u)` for a unitary `u in A_0`.
Approximate `u` in `2`-norm by a unitary `v` supported on finitely many
coordinates (finite tensor subalgebras are strongly dense, and polar
correction stays in the same finite-dimensional algebra).  Choose `n` so
that both `n` and `n+1` are outside that support, and put a trace-zero
unitary `a` in coordinate `n`.  Then `v` commutes with `a`, so sufficiently
good approximation gives

```text
||u a u* - a||_2 < 1.
```

On the other hand `u a u*=sigma(a)` lies in coordinate `n+1`.  Product-trace
independence and `tau(a)=0` give

```text
||sigma(a)-a||_2^2=2,
```

a contradiction.  Thus the bilateral shift is outer.

For every finite set of tensor coordinates, however, the shift on that set
extends to a permutation of a larger finite coordinate set.  The associated
finite tensor-permutation unitary implements `sigma` exactly on the original
finite set.  Along an increasing exhaustion these unitaries `(u_k)` satisfy

```text
||u_k x u_k* - sigma(x)||_2 -> 0             (x in A_0).
```

Therefore `(u_k)_omega in A_0^omega` implements the diagonal copy of
`sigma`.  This is the precise coherence supplied by the ultrapower and
missing inside the original factor.

The same calculation applies to an infinite tensor tower of finite marked
Clifford blocks: the central sign can be fixed inside each block, but a
stable-letter shift through infinitely many blocks is outer in the block
factor and only approximately inner.  Passing to the canonical crossed
product spatializes it at the cost of the expected nonamenable `L(V)`.
Accordingly, a viable `w |-> -1` character must use a nonregular
representation of `V` and a larger hyperfinite ambient inclusion; the
canonical block tower cannot be diagonalized from `R^omega` into `R`.
