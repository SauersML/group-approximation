# One universal seed for the ring theorem

2026-09-07.  Audit of a sixth forwarded dossier: prove the ring obstruction
once over a single fixed ring, transfer it by normal generation, and read off
a marked torsion generator and a finitely presented universal obstruction.
Everything below was re-derived here.  The Cairn provenance the dossier
reports is accurate: all five nodes it names exist and say what it says, and
`GroupApproximation/Leavitt/RankTwoCompression.lean` is present.

## Verified

**The seed ring.**  `C = Z<s_0,s_1,t_0,t_1 | t_i s_j = delta_(ij)>` acts on
the free abelian group on finite binary words with `s_i` prefixing and `t_i`
deleting a matching prefix, so `C` is nonzero of characteristic zero, and
`s_0t_0 + s_1t_1` is the projection off the empty word, not `1`.  With
`e = 1 - s_0t_0`, `t_1 e s_1 = t_1s_1 - (t_1s_0)t_0s_1 = 1`, so `C` satisfies
the manuscript's hypothesis with the single-product fullness witness.  `C` is
finitely generated as a ring, and `EL_4(C)` is finitely generated as a group,
since `e_(ij)(r)e_(ij)(r') = e_(ij)(r+r')` and
`[e_(ik)(r), e_(kj)(r')] = e_(ij)(rr')` reach every coefficient from the five
values `1, s_0, s_1, t_0, t_1` in rank four.

**Universality.**  `C` is presented by exactly the splitting relations, so
any four elements of any unital ring with `w_iv_j = delta_(ij)` define a
unital map `C -> R`.  By `full-idempotent-ring-has-properly-infinite-unit`
such elements exist in every ring satisfying the manuscript's hypothesis.

**The signed swap.**  `a = e_12(1)e_21(-1)e_12(1) = [[0,1],[-1,0]] (+) I`.
Then `a^2 = -I_2 (+) I` and `a^4 = 1`.  Since `a e_1 = -e_2` and `a e_2 = e_1`
with coordinate 3 fixed, `a e_13(r) a^(-1) = e_23(-r)`, so

```text
[e_13(r), a] = e_13(r) e_23(r).
```

Conjugating by `e_12(1)` fixes `e_13(r)` and sends `e_23(r)` to
`e_13(r)e_23(r)`, giving `e_13(2r)e_23(r)`, so

```text
[e_12(1), [e_13(r), a]] = e_13(2r)e_23(r) e_23(-r)e_13(-r) = e_13(r).
```

No characteristic is used.  Unwinding, `e_13(r)` is a product of four
conjugates of `a` or `a^(-1)`, and index permutations move `(1,3)` anywhere.

**The bound of sixteen.**  `Psi(e_13(1)) = diag(1 + S_1T_3, 1)` is the normal
generator `D` of `properly-infinite-unit-rank-two-normal-generator`, every
elementary generator of `EL_2(R)` is four conjugates of `D^(+-1)`, and `D` is
the image of an element that is itself four conjugates of `a^(+-1)`.  The
conjugators compose inside `EL_2(R)`, so sixteen.

**The finitely presented cover.**  For `A` unitary with `||A-I|| < 1/2`,
`A^4 - I = (A-I)(I + A + A^2 + A^3)` and
`||I+A+A^2+A^3-4I|| <= 6||A-I|| < 3`, so the second factor inverts with norm
at most one and `||A-I|| <= ||A^4-I||`.  With `x_1^4` among the relators this
is a linear step needing neither perfectness nor a quadratic absorption.
The threshold `||A-I|| < 1/2` still costs one compactness argument, so the
constant is existential exactly as in
`full-mf-radical-linear-relator-inequality`.

## The one cost the dossier could not see

`C` has characteristic zero.  In this repository the Ershov--Jaikin-Zapirain
input is unconditional only in prime characteristic
(`PropertyT/FinitelyGeneratedRing.lean`); the general coefficient case is
reduced in `PropertyT/EJZIntegralReduction.lean` to

```text
FreeIntegralGeneralRankElementaryPropertyT :
  forall X [Fintype X] n, 3 <= n ->
    HasKazhdanPropertyT (elementaryGroup (Fin n) (FreeAlgebra Z X))
```

which is the open residue.  `C` is a quotient of `FreeAlgebra Z` on four
generators, so property (T) for `EL_3(C)` rests on exactly that statement and
on nothing weaker.

For the manuscript this costs nothing: Ershov--Jaikin-Zapirain is published
for every finitely generated ring.  For the formalization it inverts the
present position, where the characteristic-two headline is unconditional and
only the general characteristic-zero statement is conditional.  So the
recommendation recorded here is to use the seed for the **general ring
theorem**, where characteristic zero is already the ambient case, and to
leave the binary headline computing in characteristic two.  The node
`universal-seed-group-collapses-elementary-groups` carries this note.

## What §6 does and does not remove

The torsion corollary removes property (T) from the ambient group `G`.  It
does not remove it from `L`, so it does not avoid Ershov--Jaikin-Zapirain and
in particular does not avoid the residue above.

## Relation to what is already recorded

- `char-two-basis-swap-normally-generates-elementary-group` is the
  characteristic-two case, where `tau_12` has order two and `e_13(r)^2 = 1`
  performs the cancellation.  The signed swap has order four and the
  cancellation is `e_13(2r)e_13(-r) = e_13(r)`, so the general statement is
  not a restatement of it.
- `torsion-normal-generator-has-full-support-corona-core` and
  `torsion-normal-generator-mf-shadow-equivalence` are the block-restriction
  ingredients of §6, both established.
- `finitely-presented-full-radical-uniform-relator-gap` is the qualitative
  predecessor of the linear certificate.  My earlier novelty sweep missed it;
  the key was added in commit `acfeed0d8`.
- The finitely generated variant recorded in `full-defect-ring-rank-two-proof`
  runs the rank-four theorem on a subring depending on `R`.  The seed replaces
  that by one ring independent of `R`.

## Not asserted

No literature priority.  Nothing here is formalized.  The bound of sixteen is
on elementary generators, not on arbitrary group elements, whose elementary
word length is unbounded.
