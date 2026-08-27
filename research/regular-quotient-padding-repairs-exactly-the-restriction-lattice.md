---
rg: 2
id: regular-quotient-padding-repairs-exactly-the-restriction-lattice
kind: claim
title: Regular quotient padding repairs exactly the restriction-lattice class
distinct_from:
  bs14-native-cell-padding-preserves-lattice-charge: that treats padding by cells in one local three-way incidence support; this treats padding a subgroup representation by copies of the full regular representation of one finite global quotient.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies the nonnegative fiber over an already extendible core; this identifies exactly when regular padding can put a core into that fiber.
  congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary: that gives an index lower bound for induction; this gives the exact restriction-cokernel obstruction to regular padding, even with arbitrarily many copies.
---

**ESTABLISHED.**  Let `K<=Q` be finite groups and write

```text
res:R_Z(Q) -> R_Z(K)                                      (RQP1)
```

for restriction on Grothendieck groups.  For a genuine finite-dimensional
`K`-representation `beta`, the following are equivalent:

1. for some integer `t>=0`, the representation

   ```text
   beta (+) t Res_K^Q(lambda_Q)                           (RQP2)
   ```

   is the restriction of a genuine `Q`-representation;
2. `[beta]` belongs to `im(res)`.

Thus copies of the regular quotient representation remove every
**semigroup** obstruction inside the correct restriction lattice, but they
never change the restriction-cokernel class.

The obstruction occurs in the actual BS congruence cores.  Put

```text
Q=PSL_2(F_17),
N={u(x):x in F_17},
H=<4>={1,4,16,13},
K=N semidirect H.                                        (RQP3)
```

Let `psi(x)=exp(2 pi i x/17)` and

```text
beta=Ind_N^K(psi).
```

Then `[beta]` does not even lie in the complex linear span of restrictions
of `Q`-characters.  Indeed, on `N` its character is the Fourier sum over
the orbit `H`.  The full split torus in `Q` conjugates `u(x)` by every
nonzero square.  Since `2` is a square modulo `17` but `2 notin H`, the two
Fourier sums associated with `H` and `2H` are distinct by injectivity of the
finite Fourier transform.  Hence the character of `beta` is not constant
on the intersections with `K` of `Q`-conjugacy classes.  Every restricted
virtual `Q`-character is constant there.  Consequently no number of regular
`Q` packets makes `beta` extendible.

At a fixed authenticated quotient this theorem is also the exact positive
statement one can use.  If `[beta] in im(res)`, choose a virtual
`Q`-representation `z` with `res(z)=[beta]`.  Since

```text
lambda_Q = (+)_alpha (dim alpha) alpha,                  (RQP4)
```

adding sufficiently many copies of `lambda_Q` makes every coefficient of
`z` nonnegative.  Its restriction is `(RQP2)`.  Because the representation
lattices are finite rank, for one fixed `Q` the required padding is bounded
linearly in `dim(beta)`, with a constant depending on `Q`.  Neither that
constant nor the lattice condition is uniform when the congruence quotient
moves.

