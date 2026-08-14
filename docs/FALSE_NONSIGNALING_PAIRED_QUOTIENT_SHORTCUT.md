# Perfect no-signaling pairing boxes do not produce whole maps

Date: 2026-08-14

## 1. Outcome

The paired-quotient contradiction cannot be applied directly to compatible
labelwise correlations.  In every nonzero finite perfect binary pairing of
rank at least two, there is an exact no-signaling box which wins all three
transport contexts while having the same uniform marginal at every endpoint.

Let `V` and `W` be finite binary vector spaces of the same cardinality

```text
N = |V| = |W| >= 4,
```

and let

```text
b : V x W -> F_2
```

be a perfect bilinear pairing.  Write `V* = V \ {0}` and
`W* = W \ {0}`.  For `c in F_2`, define `q_c` to be the uniform law on

```text
S_c = {(x,y) in V* x W* : b(x,y)=c}.                 (NSP1)
```

For each fixed nonzero `x`, perfectness makes `y |-> b(x,y)` a nonzero
linear functional.  Therefore

```text
|{y in W* : b(x,y)=1}| = N/2,
|{y in W* : b(x,y)=0}| = N/2 - 1.                   (NSP2)
```

The same counts hold after exchanging `V` and `W`.  Consequently both
marginals of each `q_c` are uniform on the corresponding nonzero space:

```text
sum_y q_c(x,y) = 1/(N-1),
sum_x q_c(x,y) = 1/(N-1).                            (NSP3)
```

In particular, the marginal does not depend on `c`.

## 2. Exact three-context countermodel

For every source pair `(v,w)`, use the following output laws:

```text
context 00: q_(b(v,w)),
context 01: q_0,
context 11: q_(b(v,w)).                              (NSP4)
```

Every sampled output is nonzero.  The first and third laws satisfy their
diagonal pairing equation exactly, and the middle law satisfies its
crossed-zero equation exactly.  Equation `(NSP3)` gives one common uniform
output marginal at each endpoint.  It is independent of the other party's
source and even of the local source, so `(NSP4)` is no-signaling in the
strongest elementary sense needed here.

Thus the three context-type edges can have exact compatible pair laws and
zero observed error even though the deterministic common-map theorem has a
fixed positive error floor.  There is no contradiction: `(NSP4)` selects a
new correlated output pair for every source pair.  It is not a probability
law on whole response maps.

This supplies a concrete witness for the locality gap described abstractly
in `TRUE_TREE_GLUE_COMMON_TRANSPORT_LAWS.md`.  Tree gluing can glue laws on
whole maps along the path

```text
L0 -- R0 -- L1 -- R1,
```

but it cannot turn a family of source-pair boxes into whole maps.  The
source-setting graph contains the obstruction.

## 3. Why rank one does not repair the argument

When `N=2`, the only nonzero vectors pair to `1`, so `S_0` is empty and the
construction above is unavailable.  This does not allow an arbitrary
paired-radical quotient to be replaced by a rank-one quotient.  A chosen
one-dimensional subspace need not be preserved by the four coefficient
arrows

```text
a |-> a t_i,       b |-> s_j b.                      (NSP5)
```

Restricting to a line can therefore destroy the transport relations whose
incompatibility is being measured.  The weighted robust floor already works
uniformly over all nonzero quotient ranks; the live task is to retain the
full multiplication-coherent fiber, not to select a rank-one fragment.

## 4. Consequence for the live theorem

The following implication is false, even with exact relations:

```text
compatible no-signaling label PVMs
        => a common classical law on response maps.  (NSP6)
```

Accordingly, normalized-Hilbert--Schmidt extraction must use an additional
global relation which synchronizes the raw branch decoder across every
source label in a comb extension fiber.  Equivalently, it must recover a
multiplication-coherent character decoder or a common finite-multiplicity
Cartan.  Marginal consistency, perfect pairing values, and tree gluing alone
cannot close the hyperlinearity argument.

This is a mathematical no-go result, not a computational observation.  It
has also been encoded for the smallest case `V=W=F_2^2` in
`GroupApproximation/Leavitt/FiniteNoSignalingPairingBox.lean`.  The theorem
`exists_exact_three_context_pairing_box` packages the two exact diagonal
laws, the crossed-zero law, their common marginals, and their support
conditions.  This source was added without running a local or MSI build, so
kernel checking is deliberately deferred rather than claimed.
