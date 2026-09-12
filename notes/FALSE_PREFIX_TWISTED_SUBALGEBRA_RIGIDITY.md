# Prefix death makes every twisted Leavitt algebra contain the untwisted target

Date: 2026-08-12

## 1. Outcome

Put

```text
L=L_(F_2)(1,2),       Q=L^x,
kappa(g)=s_0 g t_0+s_1t_1.                            (PTR1)
```

The established prefix-stabilization calculation gives

```text
kappa:Q->Q injective,       kappa_*=0 on H_2(Q,Z).     (PTR2)
```

This has two consequences for the current FALSE program.

1. For every circle-valued multiplier `c` on `Q`, the twisted group von
   Neumann algebra `L_c(Q)` contains a trace-preserving copy of the ordinary
   group von Neumann algebra `L(Q)`.
2. On the universal central extension, prefix stabilization kills the
   entire central kernel in one step.  Thus standard prefix refinement of a
   genuine atlas phase cannot amplify or retain that phase.

In particular, Connes embeddability of even one twisted regular algebra
`L_c(Q)` already implies hyperlinearity of the known nonsofic group `Q`.
Dogon's convergent-cocycle-family criterion is therefore an exact
reformulation here, not an easier intermediate construction.  The live
atlas model must use genuinely cross-chart mixing which is not obtained by
precomposing a fixed central sector with prefix insertion.

## 2. Every multiplier untwists on the prefix self-copy

We use a general form of the argument.

**Theorem 1 (twisted self-copy theorem).**  Let `G` be a perfect countable
group and let

```text
f:G->G
```

be an injective endomorphism such that

```text
f_*=0:H_2(G,Z)->H_2(G,Z).                              (PTR3)
```

For every normalized cocycle `c in Z^2(G,T)`, the algebra `L_c(G)` contains
a trace-preserving von Neumann subalgebra isomorphic to `L(G)`.

### Proof

Since `G` is perfect, the universal-coefficient sequence identifies

```text
H^2(G,T) ~= Hom(H_2(G,Z),T).                           (PTR4)
```

The coefficient group `T` is divisible, so there is no `Ext` term; the
perfectness assumption also makes the degree-one term vanish directly.
Naturality of `(PTR4)` and `(PTR3)` give

```text
f^*[c]=0 in H^2(G,T).                                  (PTR5)
```

Hence the restriction of `c` to the subgroup `f(G)` is a coboundary after
identifying `G` with `f(G)`.  If `u_g^c` are the canonical twisted regular
unitaries, one may therefore choose scalars `a(g) in T` so that

```text
v_g=a(g)u_(f(g))^c,       v_g v_h=v_(gh).             (PTR6)
```

Injectivity of `f` and the canonical twisted trace give

```text
tau(v_g)=0       for g!=1.                             (PTR7)
```

Thus `g |-> v_g` is an honest representation with the regular character.
The trace-preserving extension of the group-algebra map identifies

```text
W*(v_g:g in G) ~= L(G).                                (PTR8)
```

This is a von Neumann subalgebra of `L_c(G)`, proving the theorem.  End
proof.

**Corollary 2 (no easier twisted target for the Leavitt witness).**  For
`Q` and `kappa` in `(PTR1)--(PTR2)`, every cocycle `c in Z^2(Q,T)` satisfies

```text
L_c(Q) Connes embeddable  ==>  L(Q) Connes embeddable
                             ==>  Q hyperlinear.        (PTR9)
```

### Proof

Apply Theorem 1.  Connes embeddability passes to trace-preserving von
Neumann subalgebras simply by restricting an embedding into a tracial
matrix ultraproduct.  Finally, `L(Q)` is Connes embeddable exactly when `Q`
is hyperlinear.  End proof.

The implication in `(PTR9)` applies to each member of a proposed family
separately.  Thus requiring nontrivial cocycles `c_n->1` with every
`L_(c_n)(Q)` Connes embeddable cannot postpone the hard microstate problem:
the first embeddable member already supplies microstates for `Q`.

## 3. Prefix stabilization kills genuine central phases

Let

```text
1 -> H_2(Q,Z) -> U_Q --p--> Q -> 1                   (PTR10)
```

be the universal central extension.  Functoriality gives the unique lift

```text
K:U_Q->U_Q,       pK=kappa p.                          (PTR11)
```

On the central kernel, `K` is exactly the map `kappa_*`.  Equation `(PTR2)`
therefore gives

```text
K(z)=1       for every z in H_2(Q,Z).                  (PTR12)
```

The simple nonabelian group `Q` is centerless, so the central kernel in
`(PTR10)` is the whole center of `U_Q`.

This proves the following.

**Theorem 3 (prefix-phase death).**  If

```text
rho:U_Q->U(M)
```

is any unitary representation in any tracial von Neumann algebra, then the
prefix-stabilized representation `rho after K` is trivial on the whole
center of `U_Q`.  The same holds for insertion into either first-level
corner, and hence for every conjugate prefix corner.  Direct sums, tensor
products, and unitary conjugates of such prefix-stabilized representations
remain trivial on the center.

### Proof

The first assertion is `(PTR12)` followed by `rho`.  Every prefix-corner
map is conjugate to `kappa`, and inner conjugacy acts trivially on group
homology, so its lift also kills the central kernel.  The last assertion is
immediate because all the listed representation operations send the
identity to the identity.  End proof.

Under the leaf-matrix self-similarity, `kappa` is precisely transported
standard matrix stabilization.  Therefore an atlas phase which genuinely
represents a class of

```text
H_2(Q,Z) ~= R/[P,R]                                    (PTR13)
```

cannot be retained by repeatedly refining the same representation into a
prefix corner.  If a finite local block continues to display a nontrivial
phase after such a refinement, it has not yet imposed all relations from
`[P,R]`; some omitted cross-chart relation must absorb that phase in every
full quotient model.

This explains the existing global audit of the exact eight-dimensional
phase block: its persistent scalar phase and its failure on the remaining
certified-zero relations are not independent numerical phenomena.  A full
model obtained by standard prefix stabilization would have to kill the
phase by Theorem 3.

## 4. Revised construction boundary

The two most explicit FALSE certificates remain

```text
Q hyperlinear,
```

or equivalently a nontrivial tracial-ultraproduct image of its universal
cover from the exact finite atlas.  Theorems 1 and 3 remove two apparent
ways of reaching that endpoint:

* proving Connes embeddability first for a supposedly easier nontrivial
  twisted regular algebra;
* repeating one fixed local central-phase block through the canonical
  prefix self-similarity.

A viable finite-atlas sequence must instead change its actual chart
representation content or its relative cross-chart holonomy as the window
grows.  The authoritative finite seed is now the dual-number image
`(C_2)^7 semidirect A_8`, which kills the complete certified package and
strictly supersedes the order-2688 local block.  The Boolean first-order
no-go shows that merely changing subset degree or multiplicity cannot make
all four survivor classes scalar.  What the present theorem excludes is
scaling any fixed phase block by prefix replication alone.

The only inputs used here are the already proved identity `(PTR2)`, the
universal-coefficient theorem, and the canonical trace of a twisted group
von Neumann algebra.  No assumption on finite generation of the unstable
multiplier is needed.
