---
rg: 2
id: six-parahoric-finite-fiber-folds-remain-amenable
kind: claim
title: Six forty-two-branch parahoric charts remain amenable after finite-fiber folding
artifacts:
  - research/artifacts/sl3-six-chart-finite-fiber-folner-2026-08-22.md
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that gives the fixed expansion payment after the branch candidates form one PVM on the genuine infinite Schreier orbit; this proves that separately labelled charts folded through a bounded multiplicity fiber do not yet form that orbit.
  folner-multiplicity-atlases-have-vanishing-first-exit: that treats unlabelled finite coweight stencils; this retains all forty-two branch labels in each of the six native Weyl directions and permits arbitrary finite-fiber holonomy.
  amenable-finite-propagation-feedback-has-folner-tail-models: that is a general compression firewall for local rules over any amenable group; this identifies the precise native SL3 skew-product left when branch histories are recycled rather than decoded as distinct building vertices.
---

Let `L` be the `A_2` coweight lattice, identified with `Z^2`, and let

```text
V={w(1,0,-1):w in S_3}                                  (SFF1)
```

be the six root-depth translations supplied by the Weyl conjugates of
`h=diag(2,1,1/2)`.  For each `v in V`, retain all `42` labels of
`C/(C cap h_v C h_v^(-1))`, as computed by
`native-sl3-edge-parahoric-has-index-forty-two`.

Suppose, however, that branch histories are allowed to fold through one
finite multiplicity fiber `F`: for every direction-label pair `(v,i)` and
every `x in L`, choose an arbitrary permutation

```text
pi_(v,i,x) in Sym(F)
```

and put

```text
T_(v,i)(x,f)=(x+v,pi_(v,i,x)f).                         (SFF2)
```

Then the resulting `252`-label transition graph on `L times F` is amenable,
uniformly in the size of `F` and in every choice of the cocycles.  Indeed,
for any coweight box `B_N` and `A_N=B_N times F`, fullness of the fiber gives

```text
|T_(v,i)A_N symmetric-difference A_N|/|A_N|
 = |(B_N+v) symmetric-difference B_N|/|B_N|=O(1/N).     (SFF3)
```

The estimate is unchanged if the fiber permutations obey arbitrary local
inverse, link, triangle, or Weyl-holonomy identities: those identities only
restrict the `pi`'s, whereas `(SFF3)` holds for every choice of them.
Compressing the labelled permutations to `A_N` and completing them on the
boundary gives finite permutation matrices for which every fixed local word
has normalized squared defect `O(1/N)`.  Tensoring with a fixed marked
finite packet retains positive marked trace.

Therefore the six root-depth profiles and all `6*42` local branch labels do
not by themselves yield a fixed boundary inequality.  They yield the
nonamenable affine-building/Hecke graph only if different branch histories
are prevented from recycling through a bounded fiber and are decoded as
distinct atoms of one global building PVM.  Equivalently, a successful
matrix-coordinate estimate must charge cross-chart branch collisions (the
Gram overlap scalar of `forty-two-branch-gram-polar-rounding`) or prove an
approximate deck-cocycle faithfulness statement.

The conclusion persists after adjoining the native signed parahoric
triangle if that triangle is not tied to the cutoff's literal support:
`affine-weyl-folner-cut-survives-native-parahoric-triangle` gives exact finite
torus models with a joint six-direction trace-`1/42` cutoff and an exact
trivial triangle corrector.  Thus the first genuinely nonamenable datum is
not the triangle relation by itself, but its raw same-carrier source/range
incidence.

This is not an arithmetic-group countermodel: the folded cocycles need not
respect the dense integral labels of all words in `SL_3(Z[1/2])`.  It proves
that nonamenability cannot be inferred from the six marginal depth shifts,
the forty-two labels, and bounded local holonomy alone.  The remaining
arithmetic datum is precisely global branch-history consistency; once that
produces a single PVM, the established infinite-Schreier spectral gap gives
the desired fixed payment.
