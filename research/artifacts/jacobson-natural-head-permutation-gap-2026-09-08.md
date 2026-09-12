# A sharp sqrt(3) gap for natural-head permutation packets

2026-09-08. The lower bound here concerns permutation involutions in a
specified natural-head basis. It does not give a lower bound for arbitrary
unitary involutions, even on the same packet. The explicit upper-bound
example does apply to the unrestricted Jacobson two-braid infimum.

Let `G=GL_3(F_2)`, let `Omega=F_2^3\{0}` with the natural action, and
let `T` be any nonempty finite `G`-set. The exact packet acts on

```text
Omega x T,       (g_Q,g_P)(v,t)=(g_Q v,g_P t).
```

Put `K=GL(<e_1,e_3>)_Q`, `B=(w_23,w_23)`, and `D=(1,w_13)`.
Throughout Sections 1--2, `H` is a permutation involution commuting
with `K`. Permutations act on the corresponding complex orthonormal
basis when operator norms are taken.

## 1. The first braid cannot hold

Write `U=<e_1,e_3>`, and split the head points into

```text
{e_2},           U\{0},           e_2+(U\{0}).             (1)
```

The first set is the `K`-fixed set, and each of the other two carries
the natural permutation action of `S_3` on three points. That action
has trivial permutation centralizer. Consequently a `K`-central
permutation has the form

```text
H(e_2,t)=(e_2,h_0(t)),
H(v+c e_2,t)=(v+c' e_2,t'),    (c',t')=h_1(c,t),          (2)
```

where `v in U\{0}`, `c in {0,1}`, `h_0` is a permutation of `T`,
and `h_1` is a permutation of `{0,1} x T`. They are involutions
when `H` is. The same `h_1` acts at all three values of `v`.

Suppose, for a contradiction, that `(HB)^3=1`. Start at `(e_2,t)`.
After `B`, the head coordinate is `e_3`. If the next `H` leaves it
in the family `U\{0}`, it is still `e_3`. The next three head
coordinates, after `B,H,B`, are then `e_2,e_2,e_3`.
The final `H` cannot send the nonfixed `K`-orbit of `e_3` into the
fixed set. Thus that case cannot return to `(e_2,t)`.

Since the tail action of `w_23` is a bijection, the braid at all
points `(e_2,t)` therefore forces

```text
h_1({0} x T) subset {1} x T.
```

These sets have the same finite cardinality. Involutivity now gives a
bijection `f:T->T` such that

```text
H(v,t)=(v+e_2,f(t)),
H(v+e_2,t)=(v,f^(-1)(t))       (v in U\{0}).             (3)
```

Apply `(HB)^3` instead at `(e_1,t)`. Using (3), its successive head
coordinates after each `B,H` are

```text
e_1, e_1+e_2, e_1+e_3, e_1+e_2+e_3,
e_1+e_2+e_3, e_1+e_3.
```

The last coordinate differs from `e_1`, a contradiction. This proves
the impossibility of the first braid without using the second braid
or any further information about the tail action.

For a nonidentity permutation `P`, one of its cycles has length
`l>=2`. On that cycle its eigenvalues are all `l`-th roots of unity.
If `l` is even then `||P-I||=2`; if `l` is odd then
`||P-I||>=2 cos(pi/(2l))>=sqrt(3)`. Applying this to `(HB)^3` gives

```text
||(HB)^3-I|| >= sqrt(3).                                 (4)
```

In particular, making the natural-head permutation packet larger cannot
drive either the first-braid defect or the maximum of the two defects
to zero.

## 2. A 56-point example attains the bound with the tail braid exact

Take `T=G/L`, with left multiplication on left cosets, where

```text
s=(2,4,3),             n=(1,4,6),              L=<s,n>.     (5)
```

A triple here encodes the columns of a binary matrix, with integers
`1,2,4` encoding `e_1,e_2,e_3`. Direct binary multiplication gives
`s^7=n^3=1` and `n s n^(-1)=s^2`. The element `s` has order seven
and `n` has order three, so `L` has order 21 and `T` has eight points.
Use these ordered coset representatives:

```text
(1,2,4), (1,2,5), (1,2,6), (1,2,7),
(1,3,4), (1,3,5), (1,3,6), (1,3,7).                     (6)
```

They yield the following tail permutations, on labels `0,...,7`:

```text
b_T=(0 2)(1 7)(3 4)(5 6),
d_T=(0 5)(1 2)(3 4)(6 7).                                (7)
```

Define `H` by (2), using

```text
h_0=(0 1)(2 3)(4 5)(6 7),
h_1=(0 5)(1 10)(2 13)(3 4)(6 11)(7 14)(8 9)(12 15),      (8)
```

where `h_1` uses label `8c+t` for `(c,t)`. Formula (2) proves
`H^2=1` and `[H,K]=1` directly. The tail involution on these sixteen
labels is `d_1(8c+t)=8c+d_T(t)`.

The nontrivial cycles of `h_0 d_T` and `h_1 d_1` are respectively

```text
h_0 d_T: (0 4 2)(1 3 5),
h_1 d_1: (1 13 9)(2 10 8)(6 14 12)(7 11 15).             (9)
```

All omitted points are fixed. Therefore `(HD)^3=1` exactly.

For a fully explicit check of the other product, label `(e_2,t)` by
`t`, and label `(v_j+c e_2,t)` by `8+3(8c+t)+j`, where
`(v_0,v_1,v_2)=(e_1,e_3,e_1+e_3)`. The full cycle decomposition
of `HB` is

```text
(0 48 30)(1 51 15)
(2 24 7 39 36 45 27 4 21)
(3 18 5 42 54 33 12 6 9)
(8 47 43 55 34 13 44 22 26)
(10 11 50)
(14 23 41 19 53 40 37 46 28)
(16 35 52)(17)(20)(25 29 38)(31 32 49).                  (10)
```

It has four nine-cycles, six three-cycles, and two fixed points.
Thus `(HB)^3` has twelve three-cycles and twenty fixed points, giving

```text
(HB)^9=1,       (HB)^3!=1,       ||(HB)^3-I||=sqrt(3).    (11)
```

The mark `w=(I+E_13,1)` swaps two pairs of natural head points, so
its negative eigenspace has dimension `2*8=16`. In particular the
example retains the mark and is admissible in the unrestricted
definition of `gamma`. Therefore

```text
gamma <= gamma_tail <= sqrt(3).                         (12)
```

Together with (4), this proves that the infimum over these natural-head
permutation packets is exactly `sqrt(3)`, whether the objective is just
the first defect, the maximum of both defects, or the first defect with
the tail braid required to be exact.

## 3. Exact finite replay and its scope

The standard-library verifier/search is
`experiments/jacobson_56_point_two_braid_search.py`. It enumerates the
168 binary matrices, verifies all `168^2=28224` products in the
coset action, and exhausts the exact-tail permutation completions of
this 56-point packet.

For completeness of that enumeration, `D` is fixed-point-free. Since
involutions with `(HD)^3=1` are conjugate, `H` is fixed-point-free too.
The union of their two matchings has components consisting of either
one common edge or an alternating hexagon. Partitioning the `D` edges
into singletons and triples, and choosing one of eight hexagon matchings
for each triple, therefore enumerates every possibility in (2).
There are

```text
1+C(4,3)*8 = 33                            choices for h_0,
1+C(8,3)*8+C(8,3)*C(5,3)*8^2/2 = 18369    choices for h_1.
```

The exact scan checks all `606177` pairs. It finds no joint braid
completion and `47520` choices with first defect below two. The minimum
first defect is `sqrt(3)`, independently confirmed by (4) and (8)--(11).
No floating point enters a relation or norm certificate; odd cycle
lengths determine the norm exactly.

The final replay ran on MSI with `/usr/bin/python3.12`, a 45-second
timeout, and one Python process. It finished successfully in 1.738
seconds. The complete output is
`research/artifacts/jacobson-56-point-two-braid-2026-09-08.json`.

```text
script SHA256:
c6ede41282c2dbe39b86f793499b356e43dae2795cc6dbe09fb3539556b83ab0
output SHA256:
715268c5915bcac2f508167b3ae072c06031ea668dbf2c25e35904a055de80da
```

The lower bound uses the fact that `H` is a permutation in the displayed
natural-head basis. A general unitary in the `K` commutant may mix
linear combinations of the three-point orbits and is not described by
(2). Even on this same complex 56-dimensional packet, its first-braid
infimum is not determined here. Other finite permutation actions of the
full packet, with different head orbit types or additional head-fixed
orbits, are also outside the lower bound.

The independent [amenable seven-ray countermodel](jacobson-two-braid-seven-ray-countermodel-2026-09-08.md)
proves `gamma=gamma_tail=0` for unrestricted unitary packets. There is
no conflict: the sharp `sqrt(3)` lower bound here shows that its
asymptotic models cannot all belong to this specified natural-head
permutation class. The result rules out that family of finite
countermodel searches; it supplies no obstruction to the unrestricted
asymptotic models.
