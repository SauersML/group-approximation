---
rg: 2
id: coinduction-algebraic-envelope-proof
kind: route
title: Compare the coinduced probability inclusion with the induced semifinite corner
target: coinduction-preserves-but-cannot-create-algebraic-envelope
requires: []
---

Choose a section `s:Lambda/H -> Lambda` with `s(H)=e`.  The usual cocycle

```text
c(g,x)=s(gx)^(-1) g s(x) in H
```

defines the coinduced action on `K_0^(Lambda/H)` coordinatewise: a coordinate
is permuted and then acted on by an element of `H`.  Since the original
`H`-maps are continuous group automorphisms, these are continuous group
automorphisms of the product compact abelian group, and product Haar measure
is invariant.

The coordinate map at `H`, `j:B_0 -> L^infinity(K)`, together with the global
crossed-product unitaries `u_h`, `h in H`, is covariant for the original
action (our normalization `s(H)=e` makes the cocycle on the fixed base coset
equal to `h`).  Hence it defines a normal star-homomorphism

```text
Phi:B_0 rtimes H -> L^infinity(K) rtimes Lambda.
```

On a finite Fourier sum, both canonical traces select the identity
coefficient, and product Haar integration of `j(f)` equals `int f dm_0`.
Thus `Phi` preserves the faithful trace and is injective.  This proves
`(CPC1)`.  Notice that the proof used the original algebraic `H`-action at
the exact point where the cocycle acts on each coordinate.  Replacing it by
arbitrary measure-preserving transformations produces a p.m.p. coinduction,
but not automorphisms of a compact abelian group.

For comparison, equip
`B_ind=ell^infinity(Lambda/H) tensor B_0` with the induced cocycle action.
Counting measure on the coset coordinate times `m_0` is invariant and gives a
faithful semifinite trace.  Let `p=1_{H} tensor 1`.  Then `p u_g p=0` unless
`gH=H`, equivalently `g in H`; moreover `p B_ind p` is canonically `B_0` and
the surviving covariance is the original `H`-action.  Fourier sums therefore
give the trace-preserving corner isomorphism `(CPC2)`.

If an invariant probability measure assigned mass `a>0` to the base coset,
transitivity would assign mass `a` to every coset, contradicting infinite
index.  Assigning mass zero makes their countable union have mass zero.  So
the induced corner has no finite invariant probability version.

Finally consider the proposed coordinate corner in compact coinduction.  It
would be supported on

```text
V={k : k_x=e for every x != H}.
```

If `K_0` is infinite, Haar measure of the identity singleton is zero, hence
`m_K(V)=0`.  If `K_0` is finite nontrivial of order `q`, then fixing any `n`
off-base coordinates has measure `q^(-n)`; continuity from above gives
`m_K(V)=lim_n q^(-n)=0`.  Thus the would-be corner projection is zero in
`L^infinity(K)`.  The only finite-trace construction is the subalgebra
`(CPC1)`, which presupposes the very algebraic envelope one hoped to create.
