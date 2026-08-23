---
rg: 2
id: kesten-chart-intersection-floor-proof
kind: route
title: Count the opposite parahoric orbit and intersect graph-product parabolics
target: kesten-chart-carriers-have-a-twenty-five-over-forty-two-gram-floor
requires:
  - stabilizer-orbit-commutators-have-a-kesten-chart-carrier
  - native-sl3-edge-parahoric-has-index-forty-two
  - native-sl3-group-is-hecke-graph-wreath-product
---

Put

```text
C=SL_3(Z),       h=diag(2,1,1/2),
D=C cap hCh^(-1),
D_0=D cap h^(-1)Ch.                                   (KIP1)
```

Then `m=[D:D_0]`.  The group `D` has the upper-root divisibilities

```text
2|g_12,       2|g_23,       4|g_13,
```

whereas membership in `h^(-1)Ch` imposes the opposite lower-root
divisibilities

```text
2|g_21,       2|g_32,       4|g_31.                  (KIP2)
```

Both groups contain the principal congruence subgroup of level four, so the
index can be counted in `SL_3(Z/4)`.  Modulo two, the image of `D` is the
eight-element lower unitriangular group.  Every element of `SL_3(F_2)` has
`2^8` lifts to `SL_3(Z/4)`.  In each of the eight relevant fibers, the
extra condition `g_13=0 mod 4` kills one independent lift bit.  Hence

```text
|D mod 4|=8*2^7.                                      (KIP3)
```

The image of `D_0` modulo two is the identity.  Its lifts are `1+2X` with
`tr(X)=0`, giving eight binary parameters.  Conditions
`g_13=g_31=0 mod 4` kill the two independent parameters `X_13,X_31`, so

```text
|D_0 mod 4|=2^6.                                      (KIP4)
```

Reduction `SL_3(Z)->SL_3(Z/4)` is onto, and the displayed congruence
conditions are exactly the definitions of `D,D_0`.  Thus `(KIP3)--(KIP4)`
give

```text
m=[D:D_0]=16.                                         (KIP5)
```

Now write `W` for the native graph-product lamp group.  For chart `i`, put

```text
V_i={a_i} union O_i.
```

The anchor `a_i` is nonadjacent to every vertex of `O_i`, so the special
parabolic on `V_i` is

```text
W_(V_i)=<c_(a_i)> * W_(O_i).                          (KIP6)
```

The free-product normal-form proof used for the Kesten carrier has the
following stronger consequence:

```text
K_i cap W_(O_i)={1}.                                  (KIP7)
```

Indeed every nontrivial freely reduced word in the generators
`[c_(a_i),c_z]`, `z in O_i`, retains an anchor syllable; the only possible
boundary cancellation is the inverse-letter cancellation already excluded
by free reduction.

For distinct `i,j`, suppose `a_j notin O_i`.  The orbital is self-paired:
a determinant-one signed long-Weyl element exchanges `hC` and `h^(-1)C`,
so `a_j notin O_i` also gives `a_i notin O_j`.  In particular
`a_i notin V_j`.  The special-subgroup intersection theorem for graph
products gives

```text
K_i cap K_j
 subset W_(V_i) cap W_(V_j)
       =W_(V_i cap V_j)
 subset W_(O_i).                                      (KIP8)
```

Equation `(KIP7)` proves the intersection is trivial.

Conversely, if `a_j in O_i`, self-pairing gives `a_i in O_j`, and

```text
[c_(a_i),c_(a_j)] in K_i,
[c_(a_j),c_(a_i)]=[c_(a_i),c_(a_j)]^(-1) in K_j.
```

This is a nontrivial infinite-order element by the free-group normal form.
Thus the paired 16-valent orbital is exactly the exceptional pair family;
the argument does not assert that its intersections are only cyclic.

There are 42 anchors and 16 exceptional neighbors at each anchor.  Hence
the number of ordered distinct pairs covered by `(KIP8)` is

```text
42*(41-16)=1050.                                      (KIP9)
```

If two subgroups `H,L` of a discrete group have trivial intersection, their
group von Neumann algebras are centered trace-orthogonal:

```text
tau(xy)=tau(x)tau(y),       x in L(H), y in L(L).      (KIP10)
```

This follows first on finite Fourier sums, since a product `hl` is the
identity only when `h=l=1`, and then by `L^2` approximation.  Apply
`(KIP10)` to `E_i,E_j` for the pairs in `(KIP9)`.  Finally
`tau(E_iE_j)=tau(E_iE_jE_i)>=0` for all projection pairs, so discarding the
exceptional terms gives

```text
G_K>=1050/1764=25/42,
```

as claimed.
