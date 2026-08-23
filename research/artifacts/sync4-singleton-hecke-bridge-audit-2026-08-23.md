# SYNC4 singleton atom equality and the signed-Hecke bridge

The singleton Culf--Mastel normal form replaces a generic binary marginal by
one equality of atom reflections.  This note computes exactly what that
changes in the existing signed-Hecke programme.

## 1. Stabilizer normal form

After putting the selected coordinate first, its atom reflection is

```text
R=diag(-1,1,1,1).
```

Over any coefficient star algebra `H`, a unitary preserves this reflection
if and only if it is

```text
diag(u,V),  u in U(H), V in U(M_3(H)).
```

Thus the selected/complement collision entries vanish, but all collisions
among the other three atoms survive.  The singleton reduction replaces the
two-fiber block structure of a general binary marginal by the particularly
clean block sizes `1+3`; it does not make the stabilizer diagonal.

The Laurent polynomial matrix

```text
1 direct_sum (1/2 [[1+z,1-z],[1-z,1+z]]) direct_sum 1
```

is an explicit finite-support unitary.  It fixes the selected atom and mixes
two complementary atoms.  Placing it on one non-tree chord after tree
gauging produces an arbitrary nontrivial Laurent holonomy invisible to all
singleton equality rows.  This is a genuine obstruction only to a compiler
that insists on coherent full-chart transports.  It is harmless to the
SYNC4 verifier once the selected atoms themselves agree on a common carrier.

## 2. Direct amalgamation fails before cycles

There is an even earlier obstruction to simply turning the exact reflection
equality into a group relator.  Amalgamate two copies of `(C_2)^4` along the
selected coordinate involution.  The group is

```text
C_2 x ((C_2)^3 * (C_2)^3).
```

In the two central sign sectors of the shared `C_2`, each local one-negative
packet projection has normalized trace respectively `1/8` and `3/8`.
Projections from the two free factors are free, so their meet has trace
`max(2 alpha-1,0)=0` in both sectors.  The two packet carriers therefore
have zero common subprojection.

The complete proof, including the strict product-norm values `sqrt(7)/4`
and `sqrt(15)/4`, is recorded in
`literal-sync4-c2-amalgam-has-zero-selected-meet` and its proof route.

## 3. Consequence for the compiler

The new Culf--Mastel lane genuinely removes arbitrary predicate
groupification, coarse marginal sums, atom-rank balancing, **and the need to
kill complementary chart holonomy**.  Only one global obligation survives:
replace the free Bass--Serre position of adjacent packet projections by a
positive canonical common carrier on which the selected reflections agree.

The target is consequently smaller than the generic signed-Hecke cycle
problem.  Full-chart transports retain a free `M_3` Laurent return, but the
verifier never reads it.  A compiler may ignore that gauge completely.  The
direct atom-reflection amalgam still fails because its packet meet is zero,
so the live target is a non-free one-edge carrier correlation, not global
complement synchronization.
