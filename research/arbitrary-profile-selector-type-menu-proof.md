---
rg: 2
id: arbitrary-profile-selector-type-menu-proof
kind: route
title: Diagonalize the normalizer action on every marked character atom
target: arbitrary-profile-selector-type-menu-dichotomy
requires:
  - root-valued-relative-transport-forces-cross-gram
---

Because `u` normalizes `H`, conjugating the Fourier idempotent gives the
group-algebra identity

```text
u e_chi u^(-1)=e_(chi^u).                              (ATMP1)
```

The Fourier idempotents of the finite abelian group `H` are mutually
orthogonal.  Multiplying `(ATMP1)` on both sides by `e_chi` proves
`(ATM2)` before applying any representation or trace.  Substituting
`u=g_1^(-1)g_2` in `(ATM3)` gives

```text
S_1^*S_2S_2^*S_1
 =pi(e_chi u e_chi u^(-1)e_chi),                      (ATMP2)
```

so `(ATM2)` proves the asserted arbitrary-profile trace dichotomy.

Identify `H` with a vector space over `F_2`, its characters with linear
functionals, and `z` with a nonzero vector.  Let `alpha` be the automorphism
induced by `u`; centralization of `z` says `alpha(z)=z`.  If `alpha` is not
the identity, choose a functional `f` moved by the dual action.  If
`f(z)=1`, it is the required moved marked character.  If `f(z)=0`, choose
`ell` with `ell(z)=1`.  If `ell` is moved, use `ell`; otherwise `f+ell` is
marked and moved.  This proves that `(ATM4)` forces `alpha=1`; the converse
is immediate.

For the exact zero model, let `O` be the finite dual orbit of a moved marked
character `chi`.  On `l2(O)`, represent `H` diagonally by the characters in
`O` and represent a generator for the cyclic action of `alpha` by the orbit
shift.  These operators represent the finite semidirect product generated
by `H` and that cyclic action.  Since `alpha(z)=z`, every character in `O`
takes value `-1` on `z`; hence `z=-1` on the whole space.  The projection
`e_chi` is a nonzero coordinate projection, while the orbit shift moves it
to an orthogonal coordinate.  Equation `(ATMP2)` is therefore zero, proving
`(ATM5)`.

For a menu, let

```text
Q_j=sum_(chi in F_j) pi(e_chi).
```

The `Q_j` are representation-level spectral cuts and `(ATM2)` gives maximal
same-atom Gram on each of them.  The normalizer unitaries identify all
character spaces in one `A`-orbit, so their multiplicities are equal.  On an
orbit `O`, the fraction captured by `Q_j` is therefore

```text
|O intersect F_j|/|O|.                                (ATMP3)
```

If every orbit meets some `F_j`, the minimum over the finitely many positive
orbitwise maxima in `(ATMP3)` is positive.  Partitioning the marked mass by
orbits and then by a maximizing `j` gives finitely many `(O,j)` pieces; one
piece has a fixed positive fraction of total marked mass and maximal Gram.
Conversely, if an orbit misses every `F_j`, its orbit representation makes
every same-atom expression `e_chi u_j e_chi` zero.  This proves the sharp
criterion `(ATM7)`.

Under the stronger cover `(ATM7a)`, every marked atom occurs in at least one
`Q_j`, so

```text
sum_j tr(Q_j)>=tr((1-pi(z))/2).
```

Pigeonhole gives one `j` with at least `1/m` of the marked mass.  This proves
the claimed stronger sufficient bound without asserting that union coverage
is necessary.

For `(ATM8)`, a transvection `alpha_w(x)=x+f(x)w` is an involution when
`f(w)=0`, and it fixes `z` when `f(z)=0`.  Its dual fixes a marked character
exactly when `chi(w)=+1`.  Taking `w=e_1` and `w=e_1+z` gives the two
complementary conditions `chi(e_1)=+1` and `chi(e_1)=-1`, proving the
two-word cover.

Finally, simultaneous row/column permutation sends the unique negative
`C_32` coordinate in `(ATM9)` to the coordinate indexed by the transported
ordered pair.  Fixing the character therefore fixes both `3` and `2`, and
hence also the remaining index `1`.  Only the identity permutation does so.
Every conjugate of this character also has trivial stabilizer, so its whole
`S_3` orbit misses the fixed set of every nonidentity group element.  This
proves failure of the sharp orbit criterion for the advertised nonidentity
`S_3` menu.

The root-valued alternative `(ATM10)` is exactly
`root-valued-relative-transport-forces-cross-gram`.  That theorem is valid
in every finite tracial representation and already includes the uniform
direct marked-root overlap estimate.  Its hypothesis concerns the literal
full-word restrictions, so it cannot be inferred from equality of typed
rectangular coefficient composites.  This proves the stated audit and its
two remaining occurrence-level alternatives.
