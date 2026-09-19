# 2026-08-18 — Finite-moment sparsification for the nonhyperlinear random-relator lane

**Status:** two elementary reductions proved below; the construction target remains open.
No nonhyperlinear group is claimed in this note.

This audit starts from the random-relator lane and removes what looked like its
main analytic obstruction.  The previous formulation tried to cover, for every
matrix dimension `n`, the full space of separated unitary tuples and then sum a
union bound over all `n`.  That pays an artificial `n^2` metric-entropy price.
For a **fixed finite relator menu** it is unnecessary.

The only observables used by the argument are normalized Hilbert--Schmidt
relator defects and normalized Hilbert--Schmidt separation of finitely many
short words.  Both are functions of finitely many normalized traces.  Hence all
finite-dimensional tuples, in all matrix sizes at once, project to one compact
finite-dimensional moment cube.  A single finite net of that cube replaces the
family of `U(n)^k` nets.

The resulting open problem is no longer a random-matrix anti-concentration
problem.  It is a finite robust-satisfiability problem:

> Find a finite menu of group relators such that every separated unitary moment
> profile violates a positive fraction of the menu, while a random sparse
> subcollection still preserves a prescribed short free ball often enough.

This is structurally a PCP/LTC condition, but with finite-dimensional unitary
moment profiles as the adversarial assignments and group relators as the local
checks.

## 1. Finite trace profiles contain every observable used by the proof

Fix free generators `x_1,...,x_k`, a finite relator menu `S` and a finite test
ball `B`.  Put

```text
W = S union {a^{-1} b : a,b in B, a != b}.
```

For a tuple `U=(U_1,...,U_k) in U(n)^k`, record only

```text
M_W(U) = ( Re tr_n(w(U)) )_(w in W) in [-1,1]^W.
```

Then

```text
d_2(r(U),1)^2 = 2 - 2 Re tr_n(r(U)),

d_2(a(U),b(U))^2
 = 2 - 2 Re tr_n(a(U)^* b(U))
 = 2 - 2 Re tr_n((a^{-1}b)(U)).
```

So both the event “this relator has defect at most epsilon” and the condition
“these tested words are delta-separated” factor through `M_W(U)`.

Let `K_delta` be the closure, in `[-1,1]^W`, of the profiles of all
`delta`-separated finite-dimensional tuples, with **all matrix sizes allowed**.
It is compact.  For any profile tolerance `eta>0`, it has a finite sup-norm net
of cardinality at most

```text
N_W(eta) <= (ceil(2/eta)+1)^|W|.
```

This bound depends on the finite word set and the requested scalar resolution,
not on matrix dimension.  Tensor amplification leaves every normalized trace
coordinate unchanged, so repeated blocks literally become one profile rather
than infinitely many copies that a dimension-by-dimension union bound counts
again.

This elementary observation retires the apparent need to prove `n^2`-scale
anti-concentration merely to pay for ambient unitary-group entropy.

## 2. Finite-moment sparsification lemma

Let `mu` be a probability distribution on the finite relator menu `S`.  Fix
thresholds

```text
0 < epsilon < epsilon_plus
```

and choose `eta` so that

```text
2 eta < epsilon_plus^2 - epsilon^2.
```

For `z in K_delta`, define

```text
p(z) = Pr_(r~mu)[ 2 - 2 z_r <= epsilon_plus^2 ].
```

Because `S` is finite, this is just the `mu`-mass of the relators whose moment
coordinate lies above the threshold.  Suppose

```text
q := sup_(z in K_delta) p(z) < 1.
```

Take an `eta`-net `Z` of `K_delta`, `|Z|=N`.  Sample `m` relators independently
from `mu`.  For any fixed `z in Z`, the probability that all sampled relators
are `epsilon_plus`-small at `z` is at most `q^m`; by the finite union bound, the
probability that **some** net point passes all checks is at most

```text
N q^m.
```

Now let `x in K_delta` come from an actual finite-dimensional tuple and assume
every sampled relator has defect at most `epsilon` at `x`.  Choose `z in Z`
with `||x-z||_infinity <= eta`.  For each sampled relator `r`,

```text
2 - 2 z_r
 <= (2 - 2 x_r) + 2 eta
 <= epsilon^2 + 2 eta
 < epsilon_plus^2.
```

Thus `z` passes every sampled relator at threshold `epsilon_plus`.  Therefore

```text
Pr[there exists a delta-separated finite-dimensional tuple
   passing all sampled relators at epsilon]
 <= N q^m.
```

This statement is uniform over **all matrix sizes** with no sum over `n`.

If, simultaneously, a preservation event `SC` saying that the sampled
presentation keeps the chosen test ball distinct has probability strictly
larger than `N q^m`, then some sample lies in `SC` and admits no separated
finite-dimensional epsilon-microstate.  The standard finite-test
characterization of hyperlinearity then excludes hyperlinearity of that
presentation.

The only remaining issue for Cairn's root word “explicit” is to extract and
certify one concrete sample rather than stop at positive probability.

## 3. What the hard theorem became

For uniform `mu` on `S`, the condition `q<1` means exactly that no separated
finite-dimensional moment profile satisfies **every** relator to
`epsilon_plus`; because `S` is finite, a uniform gap in the fraction of
satisfied relators is equivalent to `q <= 1-alpha` for some `alpha>0`.
The useful construction needs substantially more than that bare fact, however:
it must beat the preservation probability after sparsification.

A good target is therefore a finite **robust locally satisfiable relator code**:

1. **tracial/unitary soundness:** every `delta`-separated finite-dimensional
   profile violates at least an `alpha` fraction of the checks;
2. **local group satisfiability:** a random `m`-check subpresentation preserves
   a chosen nontrivial short ball with probability `s`;
3. **entropy margin:** `N_W(eta) (1-alpha)^m < s`;
4. **effective extraction:** one successful subpresentation can be named and
   its short-ball certificate checked finitely.

The thin-proof construction does **not** have this property.  If a long chain
of `M` relators only becomes contradictory when every link is present, then a
profile can satisfy `M-1` checks, so `alpha=1/M`, while preserving the forbidden
consequence under random sampling costs a coupon-collector probability on the
same exponential scale.  The finite-net factor then kills the argument.  The
checks must contain redundant global soundness, not merely a long derivation.

Likewise, a classical commuting parity/LTC construction by itself is not
enough: sparse surviving parity systems present finite or residually finite
abelian-type groups, which are hyperlinear.  The code has to be genuinely
noncommutative in the unitary/tracial sense.

## 4. Literature map: why PCP/BCS/LCS is now the natural source

Three outside bodies of work line up with the reduced target.

### Boolean constraint-system algebras

Paddock--Slofstra, arXiv:2310.07901, show that every synchronous game algebra
can be represented as a Boolean constraint-system algebra and vice versa, and
that reductions between constraint systems induce `*`-homomorphisms of the
associated algebras.  They explicitly connect dichotomy questions for
`R^U`-satisfiability with the existence of a nonhyperlinear group.  This is
almost exactly the categorical setting needed for a robust relator code: local
checks, a tracial/unitary notion of satisfiability, and algebra-preserving
reductions.

Goldberg, arXiv:2007.02782, identifies the synchronous LCS game algebra as a
quotient of the group algebra of its solution group.  Thus LCS syntax is the
most direct route from a robust constraint system to actual group relators.

### Commuting-operator PCP/compression

Lin, arXiv:2510.07162, proves `MIP^co = coRE` using a gapped compression theorem
in the commuting-operator model.  This supplies exactly the kind of robust
constant-gap noncommutative verification phenomenon that the finite-moment
lemma wants.  The missing bridge is syntactic: the verifier must be compiled
into a finite BCS/LCS/solution-group check family while preserving the relevant
tracial soundness and enough local satisfiability to sparsify it.

This is a better target than asking for dimension-dependent random-word
anti-concentration.  It asks for a **groupification of robust quantum PCP
soundness**.

### Locally testable codes

Constant-soundness quantum locally testable codes (for example
Cross--He--Natarajan--Szegedy--Zhu, arXiv:2209.11405) show that robust local
checks against global quantum data are not fantasy.  But code distance or
Hamiltonian soundness does not automatically imply the needed statement for
unitary group-word assignments; that translation is the theorem, not an
import.  This is parallel to the existing Cairn warning in
`extensive-cosystolic-index-defect`.

## 5. Relation to the AGL random-word work

Avni--Glazer--Larsen, arXiv:2402.11108, still gives valuable information:
each fixed nontrivial word has a dimension-uniform small-ball estimate on
`SU_n`, and the balanced-word repair in
`random-relator-density-repair-2026-08-18.md` transports this cleanly to the
`U(n)` setting.  But AGL is no longer being asked to pay for an `n^2`-sized
ambient net.  Its role can instead be local: prove soundness of a proposed
finite check menu, or rule out large classes of moment profiles.

The strategic change is therefore:

```text
OLD: all-dimensions U(n)^k entropy + random-word anti-concentration

NEW: fixed finite moment cube
       + robust noncommutative relator code
       + finite sparsification
       + explicit witness extraction.
```

The new middle gate is finite, combinatorial/algebraic, and directly adjacent
to PCP/BCS/LCS technology.
