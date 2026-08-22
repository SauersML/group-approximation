# Rectangle factors reduce to one Hecke letter

In the nontrivial `C_3` Fourier corner,

```text
eF_2[C_3]e congruent F_4,       e=[g]+[g^2].
```

Every nonzero `1+[r]`, `r in C_3 minus {1}`, is therefore a corner unit.  For
the five-term rectangle

```text
alpha=[h_0]+(1+[r])[x](1+[s]),
```

the `e`-component is `[h_0]e+(1+[r])[x](1+[s])`.  Invert the two edge
coefficients on the left and right.  The remaining scalar lies in `F_4^x`,
which is the order-three group represented by `[h]e`, `h in C_3`.  Absorbing
it into `x` leaves

```text
e(1+[y])e,        y notin N_G(C_3).
```

This is exact and uses no approximation or support enumeration.  It shows
that the rectangle side of `(5,7)` is not an arbitrary five-by-seven
coefficient system: after the forced C3 Fourier compression it is the
one-letter question whether identity plus one Hecke transport is one-sided
invertible.  The seven-term partner remains essential; no theorem currently
in Cairn decides this Hecke invertibility for an arbitrary letter in the
binary Leavitt unit group.
