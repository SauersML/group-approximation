# S3 packed-root retraction audit (2026-08-23)

## Question

Can the six common-source endpoint covariance rows be paid merely by naming
their orthogonally packed coefficient with one positive-root Steinberg word,
once the three target conventions and the source commutators are already
exact?

The audit tests the strongest *retractive* version of that proposal.  It
keeps the two input root lines nontrivial, checks their full finite
additivity and multiplication triangle, kills only the commutator root, and
then adjoins exact `S3` covariance and an independent faithful central twist.

## Exact payload

Work in the scalar tracial algebra and put

```text
Q=V_00=V_01=V_11=1,
Z_X=-1,       Z_Y=1,

(A_(00,X),A_(00,Y))=( 1,1),
(A_(01,X),A_(01,Y))=(-1,1),
(A_(11,X),A_(11,Y))=( 1,1).
```

All target pairs commute and are binary.  Their convention residuals are

```text
F_00=F_01=F_11=0,
```

and `[Q,Z_X]=[Q,Z_Y]=0`.  The six covariance rows are

```text
D_(00,X)=2,       D_(11,X)=2,
all other D_(b,j)=0.
```

Consequently

```text
sum_(b,j)||D_(b,j)||_2^2=8.
```

For the orthogonal row `R=sum_(j=1)^6 E_(j1) tensor D_j`, normalized matrix
trace gives exactly

```text
||R||_2^2=4/3,       6||R||_2^2=8.
```

Thus the target predicates and source commutators cannot themselves absorb
the packed mixed moment.

## Exact root escape

Over `F_5`, let the quotient of the positive-root Heisenberg group by its
center act on `F_5^2` by translations:

```text
x_12(a):(u,v) |-> (u+a,v),
x_23(b):(u,v) |-> (u,v+b),
x_13(c)=1.
```

For every `a,b in F_5`, this gives exact same-root additivity and the exact
Steinberg triangle

```text
[x_12(a),x_23(b)]=1=x_13(ab).
```

The two input roots `x_12(1),x_23(1)` are fixed-point-free nonidentity
permutations of the 25 points, while the designated packed root `x_13(1)`
is the identity.  Hence its normalized-HS defect is zero.

The audit also adjoins the standard `S3` linear action on `F_5^2`, generated
by

```text
s=[[0,1],[1,0]],       t=[[0,-1],[1,-1]],
```

and checks `s^2=t^3=1`, `sts=t^-1`, and all 50 conjugation-covariance cases.
Tensoring a faithful two-sector central `C2` representation commutes with
both factors and changes neither the payload energies nor the killed root.

## MSI replay

Script:
`experiments/s3_packed_root_retraction_audit.py`

Remote directory:
`/projects/standard/hsiehph/sauer354/cairn-s3-packed-root-20260823`

Command:

```text
/usr/bin/python3.11 s3_packed_root_retraction_audit.py
```

Environment: `acn112`, Python `3.11.13`.  The canonical JSON output has
SHA-256

```text
326043f0cf2b3c4249075ec6f3aa8aef87dbd2a0c242c47fd4a0a265f4b790f7
```

Checked results:

```text
75 root-additivity checks:                 0 failures
25 Steinberg multiplication triangles:    0 failures
50 S3 covariance checks:                  0 failures
three target convention residuals:        all zero
two source commutators:                    both zero
packed root defect squared:                0
packed covariance energy:                  8
```

## Scope

This is a decisive countermodel to a root-naming extension which retracts
after all root generators are killed.  It is not a countermodel to a new
non-retractive mixed relation that reflects the kernel of the designated
root coordinate back to the concrete row coefficient.  Rather, it proves
that such kernel reflection is exactly the missing content: root
additivity, positive-root multiplication, `S3` covariance, central twists,
the three convention equations, and the source commutators do not imply it.

