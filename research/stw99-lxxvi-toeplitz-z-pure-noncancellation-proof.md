---
rg: 2
id: stw99-lxxvi-toeplitz-z-pure-noncancellation-proof
kind: route
title: Use the Toeplitz index boundary and ideal-local K0 protection
target: stw99-lxxvi-toeplitz-z-pure-noncancellation
requires:
  - stw99-lxxvi-ideal-local-k0-protection
---

Tensor the Toeplitz extension

```text
0 -> K -> T -> C(S^1) -> 0
```

with Z.  Nuclearity makes the resulting sequence exact.  Naturality of the
six-term sequence and the Kunneth computation for Z show that the boundary

```text
K_1(C(S^1) tensor Z) -> K_0(K tensor Z)
```

is an isomorphism, just as for the original Toeplitz extension.  Exactness
therefore makes

```text
K_0(K tensor Z) -> K_0(T tensor Z)
```

the zero map.

Inside a matrix stabilization of `K tensor Z`, take `p` and `q` corresponding
to constant finite-rank projections of ranks two and one.  Their `K_0` classes
in the ideal differ by the generator, while both map to zero in `K_0(A)`.
They cannot be Murray--von Neumann equivalent in `A`: any implementing partial
isometry would equal `qvp` and hence lie in the ideal, contradicting their
different ideal `K_0` classes.  Thus their compact Cu classes are distinct.

Finally,

```text
A tensor Z ~= T tensor (Z tensor Z) ~= T tensor Z = A,
```

so `A` is Z-stable, pure, and Cu-regular.  Alternatively,
`stw99-lxxvi-ideal-local-k0-protection` directly shows that the displayed
ideal-local difference survives another tensor factor of Z.
