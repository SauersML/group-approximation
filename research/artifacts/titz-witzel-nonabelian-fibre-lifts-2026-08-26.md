# Nonabelian fibre lifts of the two-generator Titz--Witzel gate

This report attacks the remaining two-generator soficity gate through finite
nonabelian fibres.  It separates one general proof-level obstruction from two
finite computational searches.  No positive asymptotic family was found.

The accompanying reproducible programs are:

* `titz-witzel-regular-fibre-lift-check.py` for regular fibres
  `S3,D8,Q8,A4,H_p`;
* `titz_witzel_two_block_lift_search.cpp` for arbitrary two-block fibre
  permutations and a transitive annealing mode.

## 1. Normal form for a lift over the exact `C2` quotient

Let the carrier be `X x {0,1}`.  A lift in which both generators induce the
nontrivial permutation of the two blocks and in which `e^2=1` is conjugate by
a blockwise change of fibre coordinates to

```text
e(x,0)=(x,1),       e(x,1)=(x,0),
u(x,0)=(A(x),1),    u(x,1)=(B(x),0).                 (NF1)
```

Indeed, the two fibre maps of `e` are inverse, and one of them can be removed
by changing coordinates in one block.  Thus `(A,B)` is the complete voltage
data after gauge normalization.  The square and the marked word act by

```text
u^2|_{X x {0}}=B A,       u^2|_{X x {1}}=A B,
u^8|_{X x {0}}=(B A)^4,   u^8|_{X x {1}}=(A B)^4.    (NF2)
```

The two marked holonomies are conjugate, so they have equal support.

The scripts evaluate the four involution-sandwich relators

```text
c^2,        rho^2 e u^(-1),        p u d^(-1),        p u p c,
```

where `p=beta a`, together with the mark `u^8`.

## 2. Proof: regular deck transformations can never solve the gate

Suppose a finite group `F` acts regularly on `X=F`, and take `A=L_a` and
`B=L_b` in `(NF1)`.  Every even word preserves the two blocks.  On each block
it is a left translation by its fibre holonomy.  A nonidentity translation
moves every point.  Consequently each relator defect lies in

```text
{0, 1/2, 1}.                                             (R1)
```

Now consider any sequence of such regular packets.  If all four normalized
relator defects tend to zero, each of them is exactly zero from some point
on.  The packet then gives an honest homomorphism from `barGamma` to a finite
symmetric group.  The word `u^8` belongs to the simple index-two finite
residual and is killed by every finite quotient of `barGamma`.  Therefore its
defect is eventually zero.  This contradicts the separation requirement.

Hence **no sequence of regular nonabelian fibre lifts can prove soficity**.
This applies to arbitrary finite fibres, not merely the named groups tested
below.

There is a useful stronger formulation.  Let `H_n <= Sym(X_n)` contain the
two voltage permutations, and write

```text
lambda_n = min { |supp(h)|/|X_n| : 1 != h in H_n }.
```

Every relator holonomy is in `H_n`.  If the marked holonomy is nontrivial,
at least one relator holonomy is nontrivial; otherwise the four equations
would define an exact finite quotient and would kill the mark.  Therefore

```text
max_i defect(R_i) >= lambda_n/2.                           (R2)
```

It follows that any successful two-block voltage family must satisfy

```text
lambda_n -> 0.                                            (R3)
```

So replacing an abelian regular fibre by a nonabelian regular fibre is not
enough.  A viable monodromy action must contain nonidentity elements of
vanishing relative support, or must leave the constant-voltage framework.

Direct products do not improve regular packets.  In a product fibre, a block
holonomy is the identity exactly when every coordinate holonomy is the
identity.  Defect indicators are coordinatewise ORs.  A marked coordinate
already has full marked support, while adding factors can only increase each
relator defect.  Thus neither repeated powers nor mixtures of the finite
packets below improve the defect/mark ratio.

## 3. Exhaustion of named regular fibres

The Python checker derives the two block-holonomy words symbolically and
exhausts all pairs `(a,b) in F^2`.  A defect vector records the number of bad
blocks for the four relators, so each entry must be divided by `2` to obtain
normalized Hamming defect.  Every nonzero mark below has two bad blocks and
hence normalized defect `1`.

| fibre | order | pairs | marked pairs | exact pairs | best marked defect blocks | mark blocks |
|---|---:|---:|---:|---:|:---|---:|
| `S3` | 6 | 36 | 12 | 1 | `(0,2,2,2)` | 2 |
| `A4` | 12 | 144 | 96 | 1 | `(2,1,1,2)` | 2 |
| `D8` | 8 | 64 | 0 | 1 | none | 0 |
| `Q8` | 8 | 64 | 0 | 1 | none | 0 |
| `H_3` | 27 | 729 | 702 | 1 | `(2,1,1,2)` | 2 |
| `H_5` | 125 | 15,625 | 15,500 | 1 | `(2,2,2,0)` | 2 |
| `H_7` | 343 | 117,649 | 117,306 | 1 | `(2,2,1,1)` | 2 |

For every fibre that carries the mark, the best total normalized relator
defect divided by normalized mark is exactly `3`.  In `D8` and `Q8`, every
element has fourth power one; `(NF2)` therefore makes the mark identically
trivial.  In every row the unique exact pair is the trivial pair, as verified
by exhaustive enumeration.  These finite facts are evidence only; the
regular-lift obstruction in Section 2 is the general proof.

## 4. Exhaustion of arbitrary two-block permutations

The C++ program next allows arbitrary `A,B in Sym(X)`, rather than regular
translations.  Simultaneous conjugation sends `A` to a canonical
representative of its cycle type, after which enumerating every `B` covers
all pairs up to conjugacy.  The program also restricts to pairs for which
`<A,B>` is transitive, excluding improvements obtained merely by padding a
small marked component with fixed components.

The following table gives exact exhaustive results.  Defects and marks are
unnormalized supports on the full `2m`-point carrier.  "Best sum" minimizes
`sum(defects)/mark`; "best max" minimizes `max(defects)/mark`.

| `m` | normalized candidates | transitive | marked transitive | best sum `(defects; mark)` | best max `(defects; mark)` |
|---:|---:|---:|---:|:---|:---|
| 1 | 1 | 1 | 0 | none | none |
| 2 | 4 | 3 | 0 | none | none |
| 3 | 18 | 12 | 6 | `((0,4,4,4);6)` | same |
| 4 | 120 | 80 | 26 | `((0,4,4,4);6)` | same |
| 5 | 840 | 548 | 336 | `((0,8,8,8);10)` | same |
| 6 | 7,920 | 5,408 | 3,752 | `((0,8,8,8);12)` | same |
| 7 | 75,600 | 51,648 | 43,360 | `((0,12,12,12);14)` | `((10,10,10,10);14)` |
| 8 | 887,040 | 628,608 | 546,400 | `((0,13,14,12);16)` | `((12,12,12,12);16)` |
| 9 | 10,886,400 | 7,824,432 | 7,258,208 | `((0,15,13,8);18)` | `((12,13,13,13);18)` |

There is no downward trend toward zero in either ratio through `m=9`.  This
is not an asymptotic lower bound.

Transitivity-preserving annealing also failed to find a scalable hint:

| `m` | steps | defect support | mark support |
|---:|---:|:---|---:|
| 20 | 100,000 | `(24,37,36,32)` | 40 |
| 40 | 200,000 | `(64,75,76,77)` | 80 |
| 80 | 300,000 | `(136,154,158,158)` | 160 |

These annealing rows are heuristic and make no impossibility claim.

## 5. Reproduction

```text
python3 research/artifacts/titz-witzel-regular-fibre-lift-check.py

c++ -O3 -std=c++17 -Wall -Wextra -pedantic \
  research/artifacts/titz_witzel_two_block_lift_search.cpp -o /tmp/tw2block
/tmp/tw2block exhaust 9
/tmp/tw2block anneal 20 100000 2026082601
/tmp/tw2block anneal 40 200000 2026082602
/tmp/tw2block anneal 80 300000 2026082603
```

## 6. Honest endpoint

No nonabelian fibre family closes the soficity gate.  The useful gain is a
sharp change in the design specification:

* regular deck monodromy is now ruled out for every finite fibre group;
* products of regular packets cannot improve it;
* any constant-voltage two-block family must use permutation groups whose
  relative minimal degree tends to zero;
* exhaustive arbitrary transitive fibres through size nine and larger
  heuristic searches show no positive pattern.

The next credible computational target is therefore not another small
regular group.  It is a growing nonregular action (for example a natural
action of a large symmetric or iterated imprimitive group) in which the four
relator holonomies are sparse while `(BA)^4` remains macroscopically moving.
