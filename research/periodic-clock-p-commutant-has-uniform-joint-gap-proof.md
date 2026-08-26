---
rg: 2
id: periodic-clock-p-commutant-has-uniform-joint-gap-proof
kind: route
title: Average over the unit powers and then over the residual three-point fibers
target: periodic-clock-p-commutant-has-uniform-joint-gap
requires: []
---

Write `zeta=exp(2 pi i/q)` and `L=phi(q)=2*3^(n-1)`.  The powers of `2`
run through all units modulo `q`.  Define the contractive average

```text
Y=(1/L) sum_(j=0)^(L-1) D^(2^j) X D^(-2^j).          (1)
```

Because `X` commutes with `P` and

```text
P^j D P^(-j)=D^(2^j),
```

every summand differs from `X` by a unitary conjugate of the same
`D`-commutator.  Hence

```text
||X-Y|| <= ||[X,D]||=:delta.                         (2)
```

The average in `(1)` is a Schur multiplier.  On the `(x,y)` matrix entry
its coefficient is the normalized Ramanujan sum

```text
(1/phi(q)) sum_(u in (Z/qZ)^*) zeta^(u(x-y))
 = 1       if x=y,
 = -1/2    if x-y is +q/3 or -q/3,
 = 0       otherwise.                               (3)
```

Thus `Y` has entries only on the diagonal and on the two residual offsets
`+q/3,-q/3`.  The average `(1)` commutes with conjugation by `D`, so

```text
||[Y,D]|| <= delta.                                  (4)
```

Now put

```text
Z=(1/3)(Y+D Y D^(-1)+D^2 Y D^(-2)).                  (5)
```

On either residual offset, conjugation by `D` multiplies the entry by a
nontrivial third root of unity.  Therefore `(5)` kills both offsets and is
exactly the diagonal part of `Y`, which is also the diagonal part of `X`.
Moreover

```text
||Y-Z||
 <= (1/3)(||Y-DYD^(-1)||+||Y-D^2YD^(-2)||)
 <= (1/3)(delta+2delta)=delta.                       (6)
```

Since `X` commutes with the permutation `P`, its diagonal entries are
constant on the multiplication-by-`2^(-1)` orbits.  The same is true of
`Z`; hence `Z` commutes with both `P` and `D`.  Combining `(2)` and `(6)`
proves `(PCG2)`.  The orbit calculation giving `(PCG3)` is the one in
`higman-fourth-return-jointly-centralizes-clock-proof`.

For `(PCG4)`, put `C=K^4`.  Exact return says `[C,P]=0`, while
`higman-fourth-return-jointly-centralizes-clock` gives
`||[C,D]||<=2epsilon`; apply `(PCG2)`.

For the rate-dependent statement, average

```text
X=(1/L) sum_(j=0)^(L-1) P^j C P^(-j).                (7)
```

Then `X` commutes with `P`, and telescoping the `P`-commutator gives

```text
a:=||C-X|| <= ((L-1)/2)r.                            (8)
```

The simultaneous-centrality estimate gives

```text
||[X,D]|| <= ||[C,D]||+2a <= r+2epsilon+2a.          (9)
```

Apply `(PCG2)` to `X` and add `(8)`:

```text
dist(C,{P,D}')
 <= a+2(r+2epsilon+2a)
 =5a+2r+4epsilon,
```

which is `(PCG5)`.  No estimate for arbitrary `r->0` follows because the
factor `L` in `(8)` is unbounded.
