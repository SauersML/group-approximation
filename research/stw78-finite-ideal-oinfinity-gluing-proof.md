---
rg: 2
id: stw78-finite-ideal-oinfinity-gluing-proof
kind: route
title: Exclude layer traces, absorb O-infinity on each layer, and glue extensions
target: stw78-finite-ideal-regular-targets-solve-map
requires:
  - stw78-nuclear-strong-pi-extension-gluing
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Because the ideal lattice is finite, choose a maximal chain

```text
0=I_0 < I_1 < ... < I_m=B.                              (2)
```

Each cover has simple layer `D_j=I_j/I_(j-1)`.  The layers are separable and
nuclear.

We first prove that `D_j` has no nonzero densely finite lower semicontinuous
2-quasitrace.  Exactness makes such a quasitrace a trace.  Every densely
finite lower semicontinuous trace is finite on the Pedersen ideal; since
`Ped(D_j)=D_j`, it is an everywhere-finite positive linear functional and
hence bounded.  Regard `D_j` as an ideal in `B/I_(j-1)`.  A bounded trace on
an ideal extends to a bounded trace on the containing C-star algebra: for a
positive contractive approximate unit `(e_lambda)` of the ideal, the
canonical extension on positive elements is

```text
tau_tilde(x)=lim_lambda tau(x^(1/2) e_lambda x^(1/2)).
```

After normalization at the unit and composition with
`B->B/I_(j-1)`, this would give a normalized trace, hence a normalized
2-quasitrace, on `B`, a contradiction.

The sigma-unital simple almost-unperforated dichotomy now applies to `D_j`:
the stably finite alternative would supply exactly such a nonzero lower
semicontinuous 2-quasitrace.  Therefore every `D_j` is simple purely
infinite, hence strongly purely infinite.  Since it is also separable and
nuclear, Kirchberg's absorption theorem makes `D_j` `O_infinity`-stable.

The nuclear strong-pure-infiniteness gluing theorem now inducts along (2),
or equivalently applies Toms--Winter extension permanence with
`D=O_infinity`, to prove that `B` is `O_infinity`-stable and strongly purely
infinite.

Finally Gabe's Theorem 9.7 applies to every nuclear map from a separable
exact domain into the strongly purely infinite target `B`, giving strong
`O_infinity`-stability.  For an LXXVIII domain, nuclearity of `A` makes every
star homomorphism out of `A` nuclear.
