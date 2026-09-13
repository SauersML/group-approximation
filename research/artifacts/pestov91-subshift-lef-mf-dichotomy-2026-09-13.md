# A finite-word criterion for LEF and MF in elementary rank four

2026-09-13. Written proof, not Lean-verified. This joins the subshift
construction answering Pestov 9.1 to the manuscript's one-sided-inverse
MF obstruction. Minimality is replaced by an exact finite-word graph
condition, for every finite alphabet and finite coefficient field.

## Theorem

Let `X` be a nonempty subshift over a finite alphabet, let `F_q` be any
finite field, and put `R_X=LC(X,F_q) semidirect_T Z`. Use
`T(x)_i=x_(i+1)` and `u f u^{-1}=f circ T^{-1}`.

For `r>=1`, the word graph has vertices `L_r(X)` and edges `L_(r+1)(X)`,
with the prefix and suffix of length `r` as endpoints. Consider

**(C)** Every edge of every word graph lies on a directed cycle.

Equivalently, at each level there are no edges between distinct
strongly connected components. For each fixed `n>=4`, the following
conditions are equivalent:

1. (C).
2. There is no clopen `U subset X` with `T(U)` a proper subset of `U`.
3. `R_X` is directly finite: `ba=1` implies `ab=1`.
4. `R_X` is stably finite: every finite matrix ring over it is directly finite.
5. `R_X` is LEF as a unital ring.
6. `EL_n(R_X)` is LEF.
7. `EL_n(R_X)` is operator MF.

All the groups `EL_n(R_X)`, `n>=3`, are finitely generated and Kazhdan.
In the positive case, `GL_m(R_X)` is LEF for every `m>=1`, in particular
the original rank-three Pestov group is LEF. In the negative case,
every elementary rank `n>=4` has an explicit nontrivial root in its MF
radical. The argument does not assert the converse in rank three.

The criterion is independent of the finite coefficient field. For
binary `X` and `q=2`, the rank-four groups have four explicit generators
of orders `7,2,2,2`. The MF locus in this parameter space is closed;
failure has a certificate in one finite word graph.

## 1. A transient edge gives an explicit one-sided inverse

Suppose (C) fails at level `r`, and choose an edge `a -> b` whose
endpoints lie in distinct strongly connected components. There is no
directed path from `b` back to `a`. Let `V` be the set of vertices
reachable from `b`, and let

`U={x in X : x_[0,r) belongs to V}`.

This is clopen, is nonempty, and excludes points whose initial word is
`a`. Reachability makes `V` forward closed, so `T(U) subset U`.
The chosen edge is realized by a point `x` with initial vertex `a`
and next vertex `b`. Thus `Tx in U` but `Tx notin T(U)`, since its
unique preimage is outside `U`. The inclusion is strict.

Write `p=1_U`, `alpha(p)=u p u^{-1}`, and define in `R_X`

`s=u p+(1-p)`, `t=p u^{-1}+(1-p)`,
`e=p-alpha(p)=1_(U minus T(U))`.

The support inclusion says `alpha(p)<=p` for these indicator functions.
It gives `(1-p)u p=0` and `p u^{-1}(1-p)=0`. Direct multiplication yields

`ts=1`, `st=alpha(p)+(1-p)=1-e`, `e!=0`.                (1)

Thus a single finite word graph supplies a direct-finiteness obstruction.
The same calculation works whenever a clopen set is strictly compressed
by `T`, without first using a graph. In characteristic `ell`, where
`ell` is the prime dividing `q`, the additive order of `e` is exactly
`ell`.

## 2. Cyclic components give finite ring models

Assume (C). Fix a large window length `h`. The level-`h-1` graph is a
disjoint union of strongly connected components, with no edges between
them. Every vertex has an outgoing edge, because words in a two-sided
subshift have extensions. Thus each component supports a closed walk
covering all of its edges: connect an enumeration of its edges by
directed paths and return to the start.

The overlap rule spells a cyclic word for each such walk. The union of
their periodic languages of length `h` is exactly `L_h(X)`. Unlike the
single-component construction, several periodic words may be needed.
Repeat each cyclic word as many times as necessary to give its chosen
matrix period `M_j` any prescribed lower bound. This repetition leaves
its language unchanged. We retain the enlarged matrix period even if
the word has a shorter primitive period.

Here is why these models prove ring-LEF, including the periodic case.
Given a finite collection of polynomial expressions in the shift units,
letter indicators and field scalars, put them in normal form

`sum_(k=-d)^d f_k u^k`,

and choose a common coefficient window `[-b,b]`. Take `h=2b+1>=2`
large enough and construct the periodic words above, with every
`M_j>2d`. Evaluate a coefficient table on the cyclic windows to get
`D_j(f_k)`, and use the permutation `P_j` of the `M_j` coordinates.
The corresponding finite matrix expression is

`sum_k D_j(f_k) P_j^k` in `M_(M_j)(F_q)`.

Each term has a different cyclic matrix diagonal, because `M_j>2d`.
Thus the tuple of matrices over all components is zero precisely when
every `f_k` vanishes on the union of their windows, which is precisely
when the original normal form is zero in `R_X`.

To make a partial ring embedding of a finite subset, choose polynomial
representatives for its elements and include their relevant differences,
sum relations and product relations in this finite list of expressions.
The preceding zero test preserves exactly those equalities and
inequalities in the finite product of matrix rings. The identity maps
to the identity. This proves unital ring-LEF.

These are models of finite tables, not homomorphisms from all of `R_X`.
The periodic words may lie outside `X`. Coefficient evaluations are
well-defined for the chosen tables because every window used in a
model occurs in `X`. In particular, a short periodic component causes
no collapse of `u^k-1`: enlarging its matrix period keeps the relevant
crossed-product degrees separate.

## 3. Complete the ring equivalences and pass to groups

A countable unital LEF ring embeds in an algebraic ultraproduct of
finite unital rings, by taking finite-table models along an exhaustion.
Each finite matrix ring over a finite ring is directly finite, since
its multiplicative monoid is finite. Applying the embedding entrywise
therefore shows that every `M_m(R_X)` is directly finite. Equivalently,
one can include all entries and products in a finite inverse-pair table.
Thus ring-LEF implies stable finiteness, which implies direct finiteness.

Section 1 says that direct finiteness excludes a compressed clopen set,
and that failure of (C) supplies such a set. Together with section 2,
this proves the equivalence of conditions 1--5.

For a finite table in `GL_m(R_X)`, include all matrix entries, their
inverse entries, and the products needed for its relations in a finite
ring table. Its finite ring model then gives invertible matrices,
preserves the prescribed products and distinguishes the prescribed
matrices. This proves LEF for `GL_m(R_X)` and its subgroups, including
every elementary rank.

LEF groups are operator MF, by finite regular unitary representations.
This proves `1 => 6 => 7`. For the reverse implication, use the
repository theorem `finite-additive-order-one-sided-defects-are-mf-invisible`,
specifically its printed one-auxiliary-coordinate proof
`torsion-defect-one-auxiliary-coordinate-proof`. It states that for a
countable ring with `ts=1` and finite-additive-order `e=1-st`, every
`e_ij(e)` lies in `Rad_MF(EL_n(R))` for `n>=4`.

The ring `R_X` is countable: every locally constant function has a
finite cylinder description, and crossed-product sums have finite
support. If (C) fails, the `s,t,e` in (1) meet all the theorem's
hypotheses. Thus

`1 != e_ij(1_(U minus T(U))) in Rad_MF(EL_n(R_X))`,      (2)

so `EL_n(R_X)` is not MF. This proves `7 => 1` and completes all seven
equivalences. It also supplies a concrete MF-radical witness from the
finite graph, rather than merely a failure of one particular model.

The MF obstruction is an application of the existing printed theorem,
not a new proof of its analytic step. Its rank restriction is essential
to the scope claimed here; the archive's rank-three one-sided-defect
problem is still open.

## 4. Kazhdan groups with four named torsion generators

The ring `R_X` is generated by `u,u^{-1}`, the finitely many letter
indicators, and finitely many field scalars. Hence it is finitely
generated as a unital ring. Elementary root addition and commutators
give finite generation of `EL_n(R_X)`, `n>=3`, and the existing
Ershov--Jaikin-Zapirain theorem gives property (T).

For binary `X` over `F_2`, use the triple `(c,t,w)` in the upper-left
three coordinates of `EL_4(R_X)`, and add the constant swap `s_34`.
The triple generates that copy of `EL_3(R_X)`. Conjugating its roots
by `s_34` gives the roots between coordinate 4 and coordinates 1 or 2.
The remaining positions follow from
`[e_31(a),e_14(1)]=e_34(a)` and
`[e_41(a),e_13(1)]=e_43(a)`. Thus these
four matrices generate `EL_4(R_X)` and have exact orders `7,2,2,2`.
The swap is elementary because the characteristic is two.

For each fixed graph level, failure of (C) depends on finitely many
language bits. Therefore (C) defines a closed subset of the space of
binary subshifts. This is exactly the MF locus, and also exactly the
LEF locus, for the rank-four family. A failing graph gives the clopen
set, ring inverse pair and radical root by the finite construction in
section 1. This does not assert an algorithm that decides the universal
positive condition after inspecting finitely many levels.

## 5. Two elementary examples and the stronger single-component condition

Let `X` be the binary subshift forbidding `10`: its points are the two
constant sequences and all their translates of a single transition
from zeros to ones. At level one its edges are `00,01,11`; the edge
`01` lies on no directed cycle. With `p=1_(x_0=1)`,

`s=u p+1-p`, `t=p u^{-1}+1-p`,
`1-st=1_(x_(-1)=0, x_0=1)`.

The last function is nonzero. Thus this explicit four-generated Kazhdan
group `EL_4(R_X)` is non-MF, with the displayed cylinder root in its MF
radical. No conclusion about soficity or hyperlinearity is drawn from
this obstruction.

In contrast, the two-point subshift `{0^infinity,1^infinity}` has two
disjoint loop components at every level. It satisfies (C), and its
ring is `F_q[u,u^{-1}] x F_q[u,u^{-1}]`, so all its matrix groups are
LEF. This illustrates why strong connectivity is too restrictive for
the full positive class.

Infinite minimal subshifts satisfy the stronger condition that every
word graph is strongly connected. That stronger condition permits one
primitive cyclic word and the finite simple expander family of the
previous theorem. Condition (C) permits several components and gives
finite products of matrix models. It captures the exact ring and
rank-at-least-four MF/LEF boundary without a minimality assumption.

## 6. Scope and verification

The new argument is the finite-word characterization of this entire
crossed-product family, joined to the existing rank-four MF obstruction.
The proof of direct finiteness versus periodic models is algebraic and
uses finite fields; no C*-crossed-product theorem is imported. The
positive and negative implications have explicit finite constructions.
These are written proofs, not Lean formalizations, and no global
priority assertion is made.

The [algebra receipt](pestov91-dichotomy-algebra-receipt-2026-09-13.json)
records an exact step-function crossed-product check of (1) in
characteristics 2, 3 and 5. The defect is an idempotent with value one
at the transition and zero elsewhere. It also checks all 128 binary
Laurent polynomials with exponents in `[-3,3]` in a constant-orbit
model with enlarged matrix period 7; their zero tests are all correct.
The single Python 3.12 process on MSI took 0.001 seconds. This verifies
the explicit inverse-pair identities and the short-period bookkeeping;
the equivalence for arbitrary subshifts is the written proof above.

The [Cairn receipt](pestov91-dichotomy-cairn-receipt-2026-09-13.json)
records successful check and preview on the archived research snapshot
at `2b7ad1e79b5810fd1aa1e574f5d93ce3c1065b3a` with the new graph nodes
overlaid. Cairn 2.13.1 parsed 10,282 claims and 10,540 routes with no
baseline or final graph errors. Both new claims resolved as established.
The single Python 3.12 process on MSI took 30.825 seconds.

The runner retained Cairn's parser, lint, solver, check and preview
policies while replacing source and HEAD loading. Artifact existence
used the exact tracked manifest plus the delta; revision-pinned artifacts
used the warm repository's Git objects. This receipt, paragraph and the
explicit spare-index identities in section 4 were added afterward;
the checked graph nodes are unchanged. These are graph-wiring checks,
not Lean verification of the mathematical proof.
