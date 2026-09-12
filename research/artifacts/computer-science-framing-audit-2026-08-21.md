# Computer-science framing audit: syntax, HS forcing, and PCP analogies

This artifact audits Sections 1--2 of the proposed computer-science report.
It preserves the useful framing while separating the proved statements from
analogies and correcting two complexity overclaims.

## 1. Syntactic complexity is not HS-forcing complexity

A finite presentation is a constant-size **syntax**.  Polynomially addressed
words and polynomial derivation area are likewise syntactic resources.  They
do not by themselves provide a dimension-independent normalized
Hilbert--Schmidt gap.

For a derivation using relator conjugates `r_1,...,r_A`, telescoping gives a
bound of the schematic form

```text
||w(U)-1||_2 <= sum_(j<=A) ||r_j(U)-1||_2.              (CS1)
```

Thus a derivation of area `A` normally loses a factor `A`.  Constant HS
forcing requires additional information: bounded filling area for the tested
word, a spectral/Kazhdan estimate, a robust game gap, or a contractive
recurrence that sums the losses.  A small presentation can hide an enormous
Dehn function, while a long addressed word can still have one-cell relative
area, as in `free-cone-shift-finitely-wordizes-recursive-clifford-tails`.
There is therefore no invariant statement that the two complexities differ
by "exactly one pair" of quantifiers or one fixed syntactic overhead.

The rigorous computability statement is narrower.  The nodes
`nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound` and
`nonhyperlinear-presentation-sigma2-bound-proof` show

```text
HYP in Pi^0_2,                 non-HYP in Sigma^0_2.     (CS2)
```

This is an upper bound.  The report's word **exactly** must be deleted unless
a `Sigma^0_2`-hardness reduction is supplied.  The phrase "nonhyperlinearity
is RE" must also be deleted: `(CS2)` has an existential scale followed by a
universal finite-dimensional obstruction, not a single semidecidable witness.
The RE-hard LCS promise problem in `taller-vidick-lcs-re-hardness` does not by
itself classify recognition of finite group presentations.

One normalization hidden in `(CS2)` is valid but should not be confused with
hardness.  A tuple that merely keeps one nontrivial word away from the
identity can be direct-summed with a trivial block, tensor-powered to make
that word's trace small, and then tensored with the corresponding tuples for
the finitely many other words.  Tensor-product relator defects telescope,
while every target trace product contains its own near-zero factor.  This
justifies using one simultaneous near-canonical-trace microstate at each
finite scale.  It proves the quantifier **upper bound**, not that the index
set is complete at that level.

## 2. The HS--PCP analogy, with its exact scope

The productive analogy is this.  A proposed nonhyperlinear compiler seeks a
fixed finite family of local group-word checks with:

- **perfect infinite/tracial completeness:** an exact representation obeys
  every relator and retains a designated nonidentity word;
- **constant finite-matrix soundness:** every finite-dimensional tuple either
  pays a constant normalized-HS relator energy or collapses that word.

This resembles a perfect-completeness quantum PCP whose soundness ranges over
all finite-dimensional strategies.  `non-ce-bcs-has-robust-approximate-energy-gap`
already supplies the robust finite BCS energy gap.  The unsolved step is
groupification without diluting that gap or destroying the exact tracial
model.

It is not literally the standard quantum PCP conjecture.  The witness
dimension is unbounded, the objective is normalized trace of word defects
rather than ground energy on a prescribed tensor-product geometry, and the
complete witness may exist only in a non-Connes-embeddable tracial algebra.
Accordingly standard local-Hamiltonian PCP theorems cannot simply be quoted
as the missing compiler.

Perfect completeness is load-bearing at the group boundary.  Exact relators
produce a homomorphism and protect the marked word.  A game strategy of value
`1-epsilon` generally produces only approximate relations.  The existing
`taller-vidick-lcs-re-hardness` theorem has constant soundness and
completeness `1-epsilon`, not one; its own framing identifies perfect
completeness as the missing implication toward a nonhyperlinear group.
The classical perfect-completeness theorem `dinur-pcp-theorem` therefore
serves as motivation, not as a noncommutative compiler.

## 3. Why the classical sofic PCP intuition stops at matrices

In a permutation approximation, each generator acts on a finite set.  A
failed relation is a set of bad points, and an expander/PCP test can sample,
copy, and route those points.  This makes local-to-global amplification
combinatorial: errors have locations.

In a unitary approximation, normalized-HS error is an average over a Hilbert
space, but there is no canonical basis in which all generators become
permutations.  Different context decompositions may be coherent
superpositions of one another.  Copying a test can rotate or redistribute the
bad subspace instead of exposing a common set of bad coordinates.  This is
the substantive reason a sofic PCP argument does not automatically prove its
hyperlinear analogue.

Property (T) is a possible wall, but its scope must be stated precisely.
`kazhdan-almost-invariant-corner-near-invariant-projection` rounds an
almost-invariant projection **inside a genuine representation**.  It does not
turn an arbitrary approximate representation into a genuine one, and it does
not align independently rounded BCS contexts.  The left--right construction
in `fixed-bcs-context-rounding-gives-commuting-strategy` illustrates the
remaining issue: every context can be rounded while living in a different
commuting realization.  A successful property-(T) compiler must first build
one shared carrier/module on which the Kazhdan action is genuine, then prove
that all contextual payloads couple to it with positive density.

The corrected CS summary is therefore:

```text
finite syntax + robust local BCS gap
  + shared noncommutative carrier/alignment
  + exact perfect-completeness model
  => candidate constant-HS group compiler.              (CS3)
```

The first and last ingredients exist in separate Cairn nodes.  The shared
carrier/alignment implication is the current wall; neither classical PCP
amplification nor property (T) alone supplies it.
