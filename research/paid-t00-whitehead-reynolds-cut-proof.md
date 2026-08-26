---
rg: 2
id: paid-t00-whitehead-reynolds-cut-proof
kind: route
title: Reynolds-average the localized Pauli compression before taking its spectral high cut
target: paid-t00-reynolds-cut-is-whitehead-reducing
requires:
  - paid-t00-pauli-menu-hits-whitehead-constant-atom
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
---

Choose `epsilon` as in `(PWR3)`.  Since the literal Whiteheads are
involutions satisfying the Coxeter braid, their generated actor group is a
quotient of `S_3`; averaging over the six displayed words, with repetitions
if the quotient is smaller, is still invariant under both generators.
Because each actor commutes with `P` and preserves `e`, `(PWR4)` is a
positive contraction below `e`, has the same trace as `A`, and commutes with
both `J_i`.

Functional calculus preserves that commutant, so `(PWR5)` commutes with both
Whiteheads.  On `e-E`, the spectrum of `B` is below `1/32`, while on `E` it
is at most one.  Therefore

```text
tau(B)<= (1/32)tau(e)+(31/32)tau(E).                  (1)
```

Using `tau(B)>=tau(P)/128` and `tau(e)=tau(P)/8` in `(1)` gives

```text
tau(E)>=(32tau(B)-tau(e))/31
      >=tau(P)/248,                                  (2)
```

which proves `(PWR6)`.

On the range of `E`, functional calculus also gives `EBE>=(1/32)E`.
Taking traces and expanding the Reynolds average yields

```text
(1/6) sum_(w in S_3) tau(EwAw^(-1)E)
 =tau(EBE)
 >=tau(E)/32
 >=tau(P)/7936.                                      (3)
```

At least one summand is at least the average.  Since `E<=e` and every `w`
preserves `e`, that summand is exactly

```text
tau(EwC_epsilon w^(-1)E).                            (4)
```

Conjugating `(PWR2)` identifies `(4)` with the paid carrier of the ordinary
word `(PWR8)`, proving `(PWR7)`.  There are eight choices of the literal
dual-Pauli flip and six choices of the native `S_3` word, so the menu has at
most forty-eight members.  Nothing in the argument identifies `E` with an
unequal Hecke selector cut; it is only a positive common reducing subcut of
the actual constant atom.
