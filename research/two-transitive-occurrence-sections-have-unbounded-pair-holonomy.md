---
rg: 2
id: two-transitive-occurrence-sections-have-unbounded-pair-holonomy
kind: claim
title: A two-transitive occurrence compiler cannot bound both endpoint holonomies
distinct_from:
  stabilizer-generator-control-has-unbounded-address-loss: that gives linear loss for one alternative name and a coherent-rotation counterexample; this proves that no choice of two global role sections can make all simultaneous pair transports have bounded stabilizer corrections.
  finite-orbit-occurrence-pauli-compiler: that asks robust game soundness to replace global observable naming; this identifies the exact section cocycle which remains even when every pairwise consistency test has one orbit.
  universal-finite-packet-library-can-be-amenable: that rules out capacity from packet abundance or positive Plancherel density; this rules out the proposed finite-orbit synchronization of one reused question carrier.
---

Let a finitely generated group `G` act two-transitively on an infinite set
`X`.  Fix distinct base points `x_0,x_1`, write

```text
H_i=Stab_G(x_i),
```

and choose arbitrary sections

```text
sigma_i:X->G,             sigma_i(x)x_i=x.             (TOH1)
```

For every ordered pair `x!=y`, choose an arbitrary simultaneous transporter

```text
g_(x,y)x_0=x,             g_(x,y)x_1=y.                (TOH2)
```

Its two endpoint holonomies are

```text
h_0(x,y)=sigma_0(x)^(-1)g_(x,y) in H_0,
h_1(x,y)=sigma_1(y)^(-1)g_(x,y) in H_1.               (TOH3)
```

Then for every pair of finite subsets `B_i subset H_i`, there is an ordered
pair `x!=y` for which

```text
h_0(x,y) notin B_0       or       h_1(x,y) notin B_1. (TOH4)
```

In particular, for the ambient word metric of the finitely generated group,

```text
sup_(x!=y) max(|h_0(x,y)|_G,|h_1(x,y)|_G)=infinity.    (TOH5)
```

If the point stabilizers are finitely generated, the same conclusion holds
for either intrinsic stabilizer word metric.

## Proof

Assume instead that all endpoint holonomies lie in fixed finite sets
`B_0,B_1`.  From `(TOH3)`,

```text
g_(x,y)=sigma_0(x)h_0(x,y)=sigma_1(y)h_1(x,y).
```

Fix one `x`.  Then every `y!=x` satisfies

```text
sigma_1(y)=sigma_0(x)h_0(x,y)h_1(x,y)^(-1)
          in sigma_0(x) B_0 B_1^(-1).                 (TOH6)
```

The set on the right is finite.  Applying its elements to `x_1` shows that
only finitely many values of `y` are possible, contradicting infinitude of
`X`.  This proves `(TOH4)`.  For `(TOH5)`, intersect each `H_i` with an
ambient word ball; these are finite.  Intrinsic stabilizer balls are finite
as well whenever the stabilizers are finitely generated.

## Consequence for occurrence consistency

Let prototype role operators be `A_0,A_1`.  A fixed-word strategy must name
the occurrence at `x` by the section word

```text
A_(i,x)=sigma_i(x) A_i sigma_i(x)^(-1).               (TOH7)
```

The literal conjugate of a two-role prototype test at `(x,y)` instead uses

```text
g_(x,y)A_i g_(x,y)^(-1)
=sigma_i(x_i') h_i A_i h_i^(-1) sigma_i(x_i')^(-1),   (TOH8)
```

where `x_0'=x,x_1'=y`.  Passing from `(TOH8)` to the fixed question operator
`(TOH7)` therefore requires the stabilizer covariance of `A_i` under the
unbounded element `h_i`.  Relations for a finite stabilizer generating set
give only the usual word-length telescope; two-transitivity and a single
pair orbit do not remove it.

The same calculation applies to a controlled swap or a partial-isometry
intertwiner placed in the prototype pair test.  Simultaneous conjugation
makes the local swap relation a zero-cost conjugate, but identifying its two
ends with the strategy's fixed question operators again inserts precisely
the two holonomies in `(TOH3)`.  Thus a finite orbit of swap tests does not by
itself produce one common Gram state or one common partial isometry.

This is a section obstruction, not a no-go for every occurrence game.  It
leaves two honest escape routes:

1. prove a dimension-independent stabilizer-covariance rounding theorem
   which controls all `h in H_i` from finitely many prototype relations; or
2. replace the highly transitive all-pairs incidence by a bounded-neighbor
   relational structure whose tested transports have uniformly bounded
   section cocycle, and separately prove that its local tests still certify
   unbounded matrix dimension.

What is invalid is the intermediate shortcut

```text
finitely many tuple orbits
   => every consistency instance has constant normalized-HS cost.
```

Finite orbit type controls the exact presentation.  It does not control the
section holonomy needed to turn contextual occurrence words into the fixed
question measurements required by robust game soundness.

## Attempts

- **Choose better transporters.**  The transporter `g_(x,y)` was arbitrary;
  the finite-set contradiction applies to every choice.
- **Use separate sections for the two roles.**  The theorem already permits
  unrelated `sigma_0,sigma_1`.
- **Put the comparison into one controlled swap.**  This localizes the test
  relation but not the identification of its endpoints with fixed question
  words; `(TOH8)` retains both holonomies.
- **Make every test occurrence a new question.**  Then the section problem
  disappears, but so does the shared-question hypothesis used by the robust
  game decoder.  Adding consistency between the new questions recreates the
  same pair-transport problem at the next incidence level.
