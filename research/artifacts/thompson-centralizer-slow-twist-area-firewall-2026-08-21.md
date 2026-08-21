# Slow order-three holonomy is a quantitative centralizer-area firewall

**Date:** 2026-08-21

## Result

In the cyclic centralizer presentation

```text
P=<b,c | b^3=1, [b,c]=1>,
```

the loops

```text
q_j=[b,c^(-j)b c^j]
```

have filling area at least linear in `j`.  The proof is a direct normalized
Hilbert--Schmidt evaluation, not a corridor heuristic.

Let `omega=exp(2 pi i/3)`, let `D=diag(omega,omega^2)`, and rotate the
eigenbasis slowly around a cyclic family of `N=8j` two-dimensional blocks:

```text
B_k=R_(2 pi k/N) D R_(2 pi k/N)^*.
```

The block sum `B` has order three exactly.  If `C` shifts the blocks, then

```text
||[B,C]-I||_2=sqrt(3) sin(pi/(4j)),
```

while shifting by `j` blocks changes the eigenbasis angle by `pi/4` and

```text
||[B,C^(-j)BC^j]-I||_2=3/2.
```

Every relator cell costs at most the first quantity under evaluation, and
the cube cells cost zero.  Therefore

```text
Area_P(q_j)
 >= (3/2)/(sqrt(3) sin(pi/(4j)))
 >= (2 sqrt(3)/pi)j.
```

## Thompson interpretation

This proves that the visible centralizer recursion in the common-pivot
Carmichael construction cannot be made uniform merely by conjugating one
shallow commutation cell through a longer and longer address word.  A slow
eigenbasis twist accumulates microscopic local errors into a macroscopic
deep commutator.

This is deliberately not stated as a lower bound in the full Bleak--Quick
presentation of Thompson `V`.  R2 and R3 may let a van Kampen diagram leave
the complement-supported centralizer and return by an ambient shortcut.
Ruling that out requires an area-undistortion theorem for the support
stabilizer inclusion, or a relation-module invariant with nontrivial
coefficients.  Ordinary scalar cell counts and ordinary low-dimensional
homology cannot supply that invariant.

## Boundary of the theorem

The result is distinct from the free-axis one-cell obstruction.  A diagram
with several cells can have arbitrarily long connector trees, so bounded
cell count does not bound cyclic boundary length.  The linear estimate here
comes from a matrix evaluation tailored to centralizer holonomy and remains
valid for an arbitrary product of interacting commutation and cube cells in
the isolated presentation.
