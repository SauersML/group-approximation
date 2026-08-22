---
rg: 2
id: native-a2-two-path-average-is-not-an-ordinary-word-compression
kind: claim
title: The native A2 two-path average is not the compression of one ordinary group word
distinct_from:
  central-hecke-controlled-multipaths-remain-sectorwise: That treats arbitrary centrally controlled sums and shows they decompose without interference; this treats the nontrivial two-path sum on one authenticated lamp corner and proves that no native monomial word realizes it.
  single-group-word-compression-unitary-normalizes-corner: That proves an abstract corner-unitarity normalization theorem; this gives the exact group-basis support obstruction for the arithmetic A2 holonomy charger before corner unitarity is assumed.
  first-root-parahoric-target-has-a-distinct-double-coset-type: That computes the two section paths and their relative parahoric holonomy; this identifies the exact missing cross term needed to feed that holonomy into the two-path leakage identity.
---

Let `c` be the native lamp involution, let

```text
P=(1-c)/2,                                             (NTA1)
```

and retain the shortest A2 section identity

```text
a=u d u^(-1)=b d,
b=x_13(2),
d=x_23(2) in D                                         (NTA2)
```

from `first-root-parahoric-target-has-a-distinct-double-coset-type`.
Because `c` commutes with `D`, the two transports

```text
A=rho(a)P,              B=rho(b)P                      (NTA3)
```

have the same source and range, and

```text
A=B rho(d)P.                                           (NTA4)
```

Their relative holonomy is the corner unitary `V=rho(d)P`.  In the
canonical regular lamp model,

```text
tau_P(V)=0,                ||P-V||_(2,P)^2=2.           (NTA5)
```

For the average `K=(A+B)/2`, the positive Gram identity therefore gives

```text
tau_P(P-K^*K)=1/2.                                     (NTA6)
```

This is exactly the desired fixed two-path leakage scalar.

# The native row does not wordize the average

There is no group element `y` in the native arithmetic-lamp group such that

```text
p rho(y)P=K,                                           (NTA7)
```

where `p=AA^*=BB^*`.  Indeed, multiply `(NTA7)` on the left by `B^*` and
put `g=b^(-1)y`.  It would imply the group-algebra identity

```text
P rho(g)P=(P+rho(d)P)/2.                               (NTA8)
```

The left side has Fourier support in the single double coset

```text
<c> g <c>.                                             (NTA9)
```

The right side is

```text
(1-c+d-dc)/4,                                          (NTA10)
```

whose support meets the two distinct double cosets `<c>` and `d<c>`;
they are distinct because `d` is a nontrivial arithmetic root element and
`d notin<c>`.  If the double coset in `(NTA9)` contained the identity term
of `(NTA10)`, then `g in<c>` and its entire support would remain in `<c>`,
so it could not contain `d`.  Linear independence of the group basis
contradicts `(NTA8)`.

Thus the actual forty-two-branch section row contains the ideal trace-zero
holonomy but not the one additive incidence that exposes it.  Its two raw
words select `A` or `B`; no ordinary third group word has compression
`(A+B)/2`.  A closing gadget must wordize this off-diagonal sum, for example
through a noncentral two-path selector, while also forcing its complementary
Julia leakage onto an already charged carrier.  Merely adjoining more
native monomial section identities cannot invoke `(NTA6)`.

