# STW Problem XCV: nonunital ASH unitization audit

## Source boundary

Seth--Vilalta, [*Continuous functions over a pure C-star
algebra*](https://arxiv.org/abs/2602.14809), Theorem B (Theorem 6.7), states
that `A tensor_min D` is pure when `A` is pure and is either simple or has
all quotients stably finite, and `D` is a **unital separable ASH algebra**.
The paper does not state the theorem for a nonunital ASH factor.

## Unitization step

The minimal unitization of a separable ASH algebra is again unital,
separable, and ASH.  This follows by unitizing a subhomogeneous inductive
system; unitizations of subhomogeneous algebras remain subhomogeneous.
Therefore Theorem 6.7 applies to `A tensor_min L_tilde`.

## Ideal step and exactness firewall

Minimal tensoring preserves injective star homomorphisms, so
`A tensor_min L` embeds in `A tensor_min L_tilde`.  It is a closed two-sided
ideal because `L` is an ideal of `L_tilde`.  This does **not** assert

```text
A tensor_min L
 = ker(A tensor_min L_tilde -> A tensor_min C),
```

an equality that would invoke exactness of `A`.  Only the ideal inclusion is
used.  Pureness passes to ideals, so the tensor ideal is pure.

The same proof works for any ideal `L` in any unital separable ASH algebra
`D`.  Applying it cell-by-cell removes the earlier unitality restriction
from the transfinite ASH-layered positive class for Problem XCV.

## Trust boundary

The imported inputs are Seth--Vilalta Theorem 6.7, standard permanence of
ASH under unitization, injectivity of the minimal tensor product, and
permanence of purity under ideals.  No abstract-to-concrete Cuntz tensor-map
identification and no assertion from the refuted first half of Problem XCV
is used.
