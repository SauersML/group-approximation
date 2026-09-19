---
rg: 2
id: type-i-minimal-tensor-reflects-to-factors-proof
kind: route
title: Tensor a non-type-I factor representation with an irreducible representation
target: type-i-minimal-tensor-reflects-to-factors
requires: []
---

We prove the contrapositive.  If `A` is not type I, it has a factor
representation

```text
rho:A -> B(H_rho)
```

whose von Neumann closure `M=rho(A)''` is not type I.  Choose any nonzero
irreducible representation `sigma:B -> B(H_sigma)`.  The spatial product
representation

```text
rho tensor sigma:A tensor_min B -> B(H_rho tensor H_sigma)
```

is min-continuous by the definition of the minimal norm.  Its von Neumann
closure is

```text
M barTensor sigma(B)'' = M barTensor B(H_sigma).       (T1)
```

This is a factor and is not type I: tensoring a non-type-I factor with the
type-I factor `B(H_sigma)` is an amplification and does not change its type.
Thus `A tensor_min B` has a non-type-I factor representation and is not type
I.  This proves that type I of the tensor product forces `A` to be type I.
Interchanging the factors gives the same conclusion for `B`.
