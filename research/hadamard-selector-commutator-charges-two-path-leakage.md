---
rg: 2
id: hadamard-selector-commutator-charges-two-path-leakage
kind: claim
title: One transverse selector commutator charges the full two-path Julia leakage
distinct_from:
  two-path-holonomy-is-paid-by-corner-leakage: that gives the abstract positive-Gram identity and leaves corner authentication open; this realizes its average and leakage as blocks of one ordinary word and charges the leakage by one ordinary commutator relator.
  centralizing-d8-word-anchors-relative-row-orientation: that anchors a binary orientation bit through a marked D8 commutator; this uses a D16 Hadamard rotation to read the complete multiplicity-valued relative holonomy between two diagonal blocks.
  controlled-linear-predication-normal-form: that lowers already available orthogonally controlled operators to parity equations; this identifies the stronger remaining input that the two desired paths must already be diagonal blocks of one ordinary selector-central word.
---

# One transverse selector commutator charges the full two-path Julia leakage

ESTABLISHED.  Let

```text
K=<z,h | z^2=h^2=(zh)^8=1>                              (HSC1)
```

be the dihedral group of order `16`.  Its faithful two-dimensional real type
may be chosen so that

```text
Z=pi(z)=[ 1  0 ],       H=pi(h)=2^(-1/2)[ 1  1 ].       (HSC2)
        [ 0 -1 ]                         [ 1 -1 ]
```

Thus `H` is the Hadamard reflection.  Work on one selected isotypic carrier
`C^2 tensor M`, and suppose an ordinary unitary return word `d` satisfies
the ordinary relation

```text
[d,z]=1.                                                (HSC3)
```

It then has the exact block form

```text
D=diag(A,B),              A,B in U(M).                  (HSC4)
```

Put `y=h d h` and let `q=(1+z)/2` be the first selector line.  One fixed
matrix multiplication gives

```text
Y=H D H=1/2 [ A+B  A-B ],
              [ A-B  A+B ]                              (HSC5)
```

so

```text
qYq=(A+B)/2,             (1-q)Yq=(A-B)/2.              (HSC6)
```

The desired arithmetic average and its Julia complement are therefore two
blocks of **one ordinary group word**, with no functional calculus.

Now add the single group-word relator

```text
[h d h,z]=1.                                            (HSC7)
```

On the selected type its normalized Hilbert--Schmidt defect is exactly

```text
||[Y,Z]-1||_2^2
 =||A-B||_2^2
 =||1-A^*B||_2^2.                                      (HSC8)
```

Here the multiplicative commutator defect equals the additive commutator
norm because multiplication by `Z` and `Y` is isometric.  In the `2 by 2`
blocks, the additive commutator has off-diagonal entries
`-(A-B)` and `A-B`; the normalized block trace proves `(HSC8)`.

Moreover the positive leakage from `two-path-holonomy-is-paid-by-corner-leakage`
is exactly

```text
tau_q(qY^*(1-q)Yq)=1/4 ||A-B||_2^2.                    (HSC9)
```

Thus `(HSC7)` charges the **entire** complementary Julia channel with a
dimension-independent, amplification-stable constant.  At zero defect it
forces `A=B`, makes `q` reducing for `Y`, and turns `qYq` into the common
corner unitary.  This is precisely the authentication required by the
two-path Gram lemma.

The relation does not kill the marked packet or a non-root assignment
projection.  In the presentation

```text
<K,d | [d,z]=1, [h d h,z]=1>,                           (HSC10)
```

the map `d->1` is a retraction onto `K`.  Hence `K` embeds and every nonzero
projection in `C[K]`, including either selector line in the two-dimensional
type, remains nonzero.  Exact models with arbitrary multiplicity also
survive by taking `D=I_2 tensor A`.

For approximate packet relations, exactification of the fixed finite group
`K`, followed by conditional expectation onto the `Z` blocks, adds only a
dimension-independent modulus.  Formula `(HSC8)` itself is exact once the
fixed packet and `(HSC3)` are exact.

## The remaining first-chord incidence

This cell does not manufacture the input word `d`.  The two desired path
holonomies must occur as the two diagonal blocks of one ordinary word which
centralizes `z`.  `piecewise-group-transport-gives-corner-unitaries` instead
produces an algebraic sum `sum_i g_i p_i` in a group-algebra corner, not a
group element.  Likewise `controlled-linear-predication-normal-form` starts
from already authenticated controlled letters; it cannot turn that sum into
one word.

Trying to declare the block equations for `d` term by term simply recreates
the signed-Hecke corner-equality compiler.  Therefore `(HSC7)` completely
solves leakage charging once a **diagonal return word** exists, and proves
that the remaining obstruction is syntactic rather than analytic: wordize
the two branch paths as the blocks of one selector-central return without
assuming the additive corner equality being sought.

