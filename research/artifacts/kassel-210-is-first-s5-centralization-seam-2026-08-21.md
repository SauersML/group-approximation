# Relation (2.10) is the first seam for the exact `S5` order-three model

Start with the exact tuple in
`kassel-through-29-has-noncentral-order-three-model`. It generates all of
`S5` and has

```text
z=w_beta^4=(0 3 4).
```

## Sequential check

Direct substitution into the remaining Kassel relations gives:

```text
(2.10) fails,
(2.11) fails,
(2.13) fails,
(2.14) fails,
(2.15) fails.
```

Thus (2.10) is the first new face. For example, its two sides are

```text
[x_(alpha+beta),x_(-beta)] = (0 1 4),
x_alpha x_(2alpha+beta)^(-1) = (1 4)(2 3),
```

and even the required commutation of the two factors on the right fails.

## Orbit covariantization cannot create a scalar omega sector

The conjugacy orbit of `z` under the generated `S5` has all twenty oriented
3-cycles. Suppose `pi` is any representation of `S5` in which `pi(z)` is
scalar. Then every commutator `[z,g]` lies in `ker(pi)`. The normal closure of
these commutators is a nontrivial normal subgroup contained in `A5`; by the
simplicity of `A5`, it is `A5`. Since `z in A5`, one obtains `pi(z)=I`.

Consequently direct sum over the conjugacy orbit, induction from the
centralizer of `z`, or any other honest `S5` covariantization cannot turn the
3-cycle into `omega I`. The omega and omega-squared eigenspaces are moved
through the full conjugacy orbit; any invariant quotient that makes `z`
scalar kills it.

## Exact degree-five enumeration through (2.10)

There is also a bounded exact audit. Enumerate `a,b,c in S5`; relation (2.4)
determines

```text
d=c^(-1)[a,b].
```

Keep the tuples satisfying `[c,d]=1` and (2.5). Enumerate `A` using (2.12),
then the square roots `B` of the common commutator in (2.6),(2.9), enumerate
`C`, and determine

```text
D=A^(-1)[b,C]
```

from (2.8). Check (2.7), both equalities in (2.10), and finally the order of
`(bB^(-1)b)^4`. This leaves exactly `6000` degree-five solutions through
(2.10), and none has a nontrivial order-three marked fourth power.

This enumeration is a finite exact statement about `S5`, not a universal
matrix obstruction. A larger finite group or genuinely projective packet
could still retain the scalar mark through (2.10).

