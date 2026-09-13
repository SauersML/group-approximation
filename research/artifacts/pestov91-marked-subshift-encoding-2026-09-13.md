# The three-generator group remembers the subshift

2026-09-13. Written proof, not Lean-verified. The previous word-problem
result computes Turing degrees. This extension gives an order and
topological embedding of the entire space of binary subshifts into
three-marked Kazhdan groups, with uniform quantitative language witnesses.

## Theorem

For every nonempty binary subshift `X`, not necessarily minimal, let

`R_X=LC(X,F_2) semidirect Z`, `G_X=EL_3(R_X)`.

Use `T(x)_i=x_(i+1)`, `u f u^{-1}=f circ T^{-1}` and `p(x)=x_0`.
Mark `G_X` by the ordered triple `(c,t,w)` from the
[unit-idempotent theorem](pestov91-three-torsion-generators-2026-09-13.md):

`c=[[0,0,1],[1,0,1],[0,1,0]]`,
`t=e_12(1-p)e_13(p)`,
`w=[[0,u,0],[u^{-1},0,0],[0,0,1]]`.

Then:

1. `X -> (G_X;c,t,w)` is a topological embedding with closed image in
   the space of three-marked groups.
2. `X subset Y` if and only if there is a marked epimorphism
   `G_Y -> G_X` (sending each named generator to its namesake).
3. All these groups are quotients of one fixed three-generated Kazhdan
   group `U`. Their marked symmetric generating sets
   `{c,c^{-1},t,w}` have a common positive Kazhdan constant.
4. `G_X` is simple if and only if `X` is infinite and minimal. In that
   case it is also LEF, hence sofic, hyperlinear and operator MF, by the
   existing subshift theorem.

Here are explicit moduli, using relation words in
`{c,c^{-1},t,t^{-1},w,w^{-1}}`:

- Agreement of the languages of `X,Y` in length `2l+1` implies agreement
  on all group relations of length at most `l`.
- There is a uniform polynomial-time construction sending each binary
  word `a` of length `n >= 1` to a group word `W_a` of length at most
  `2^17 n^2`, such that
  `W_a=1 in G_X` if and only if `a` does not occur in `X`.
  Therefore agreement on relations through length `2^17 n^2` implies
  language agreement through length `n`.

The marking is essential. This does not classify the unmarked abstract
groups up to isomorphism, or claim LEF for every nonminimal subshift.

## 1. One Kazhdan source for the entire family

Let

`B=F_2<u,v,p>/(uv=vu=1, p^2=p)`, `U=EL_3(B)`.

The algebra is nonzero (map `u,v` to `1` and `p` to `0` in `F_2`) and
is finitely generated as a unital ring. Ershov--Jaikin-Zapirain, in the
existing claim `elementary-groups-over-fg-rings-have-property-t`, gives
property (T) for `U`. The unit-idempotent theorem gives its three
generators of orders `7,2,2`.

For every `X`, mapping `u,v,p` to the shift, its inverse and the letter
idempotent gives a ring epimorphism `B -> R_X`. Surjectivity holds because
products of translates of `p` and `1-p` give cylinder idempotents, whose
sums are all locally constant functions. This argument applies equally
to periodic and nonminimal subshifts. Ring epimorphisms are onto on
elementary groups, so we obtain a marked epimorphism `U -> G_X`.

Property (T) and a Kazhdan constant for a fixed finite generating set
pass to quotients, by inflating unitary representations. Thus a positive
constant for `{c,c^{-1},t,w}` in `U` works for every `G_X`. No numerical
value for that constant is asserted.

## 2. Short relations see only short blocks

Each entry of any generator or inverse has crossed-product degree in
`{-1,0,1}`. Its coefficient functions depend at most on `x_0`.
The inverses of `t,w` are themselves, and `c^{-1}` is constant.

Expand a group word of length at most `l` by matrix multiplication. In
each product term, the partial sums of the crossed-product degrees lie
in `[-l,l]`. Thus each coefficient of its normal form

`sum_(k=-l)^l f_k u^k`

depends only on coordinates in `[-l,l]`. The coefficient tables are
computed in the full binary shift, independently of `X`, and are then
restricted to the blocks occurring in `X`. Uniqueness of the algebraic
crossed-product normal form says that a matrix is the identity exactly
when all the corresponding coefficient tables of its difference from
`I` vanish on those allowed blocks. This proves the first modulus.

It also gives a uniform nonadaptive truth-table reduction of `WP(G_X)`
to `L(X)`: on input length `l`, query only words of length `2l+1` and
evaluate the already computed tables. The number of such queries may
be exponential; no polynomial-time upper bound for this direction is
claimed.

## 3. Balanced products give quadratic language witnesses

All group words used next are fixed expressions in the marked triple;
they do not depend on `X`. Section 2 of the decoder proof supplies roots
with coefficient `p`, `1-p`, and `1`, and all constant swaps. Let `s_ij`
be the constant matrix interchanging coordinates `i,j`. Put

`d_12=w s_12=diag(u,u^{-1},1)`,
`d_13=s_23 d_12 s_23=diag(u,1,u^{-1})`,
`d_23=s_12 d_13 s_12=diag(1,u,u^{-1})`,
`V=d_13 d_23=diag(u,u,u^{-2})`.

Consequently

`V^{-a} e_12(f) V^a = e_12(u^{-a} f u^a)`.              (1)

Allow an auxiliary padding symbol `*`, with coefficient `f_*=1`, and
put `f_0=1-p`, `f_1=p`. For a decorated word `A` of length `a`, define

`f_A = product_(i=0)^(a-1) u^{-i} f_(A_i) u^i`.

Concatenation satisfies `f_(AB)=f_A u^{-a} f_B u^a`.
Starting from leaf words for `e_12(f_0)`, `e_12(f_1)` and `e_12(1)`,
construct a word `W_A` evaluating to `e_12(f_A)` by balanced recursion:

`W_(AB) = [s_23 W_A s_23,
           s_13 V^{-a} W_B V^a s_13]`.                 (2)

Indeed the first input is `e_13(f_A)`, the second is
`e_32(u^{-a}f_Bu^a)`, and their commutator is the desired `e_12(f_(AB))`.
Append `*` symbols to the input binary word until its length is a power
of two `m < 2n` (or `m=n` when already a power of two). Padding does not
alter its cylinder coefficient. This avoids repeatedly copying a word
through an unbalanced product tree.

For completeness, the decoder proof gives the following unreduced word
length bounds, with an inverse counted as one letter:

| Fixed word | Length bound |
| --- | ---: |
| `e_12(p)`, `e_12(1-p)`, `e_12(1)` | `68`, `209`, `277` |
| `e_23(1)`, `e_31(1)` | `247`, `265` |
| `e_13(1)`, `e_21(1)`, `e_32(1)` | `1048`, `1024`, `1084` |
| `s_12`, `s_23`, `s_13` | `1578`, `1578`, `2361` |
| `d_12`, `d_13`, `d_23`, `V` | `1579`, `4735`, `7891`, `12626` |

For example, `z=(ct)^4` has length `8`; `[z,t]^2` has length `36`.
Its first two conjugates by `z` have lengths `52,68`, and the commutator
giving `e_13(p)` has length `208`. Cancelling this last word from `t`
gives the bound `209`. The remaining rows follow by root addition,
spare-index commutators and `s_ij=e_ij(1)e_ji(1)e_ij(1)`.

Let `L(m)` bound the length output by (2) on a power-of-two input. Then

`L(1)<=277`,
`L(m)<=4 L(m/2)+2m*12626+4(1578+2361)`.

Summing this recurrence gives

`L(m) <= 277m^2 + 25252(m^2-m) + 5252(m^2-1)`
`      <= 30781m^2 <= 123124n^2 < 2^17 n^2`.             (3)

The recursion is an effective polynomial-time word construction. Its
value is the elementary matrix of the cylinder of the original binary
word, which is nontrivial exactly when that cylinder is nonempty. This
proves the second modulus, and in particular a uniform polynomial-time
many-one reduction `L(X) <=_m complement(WP(G_X))`.

## 4. Recover inclusion and topology

If `X subset Y`, restriction of functions induces a ring epimorphism
`R_Y -> R_X`, hence a marked epimorphism `G_Y -> G_X`. Surjectivity on
functions follows directly from their cylinder descriptions.

Conversely, let such a marked epimorphism exist. If a word `a` is absent
from `Y`, its witness `W_a` is the identity in `G_Y`, hence in `G_X`.
Thus `a` is absent from `X`. We have `L(X) subset L(Y)`, which implies
`X subset Y`: every point outside the closed subshift `Y` has a finite
cylinder neighborhood disjoint from `Y`. This proves the order statement.
Applying it in both directions proves injectivity of the marked map.

Give the space of nonempty binary subshifts its usual topology of
agreement on all blocks of bounded length. It is compact: it is the
closed subspace of shift-invariant sets in the hyperspace of nonempty
closed subsets of the compact binary shift. Give three-marked groups
the topology of agreement on relations of bounded length, equivalently
the topology on normal subgroups of the free group on three letters.
This space is Hausdorff. Section 2 proves continuity, and section 3
also explicitly proves inverse continuity on the image. Alternatively,
compactness and injectivity already make the map a homeomorphism onto
its closed image. These arguments prove the claimed topological embedding.

## 5. Simplicity detects infinite minimality exactly

If `X` is infinite and minimal, the existing subshift theorem says that
`G_X` is simple modulo its scalar centre. Over `F_2` that centre is
trivial, so `G_X` is simple and LEF.

If `X` is not minimal, choose a proper nonempty closed invariant subset
`Y`. There is a binary cylinder meeting `X` but disjoint from `Y`.
Its witness is a nontrivial element of the kernel of `G_X -> G_Y`.
The image is nontrivial, since it contains the constant element `c` of
order `7`. This gives a nontrivial proper normal subgroup of `G_X`.

Finally, if `X` is finite and minimal, it is one periodic orbit of some
length `N`. Acting on functions on that orbit gives a unital ring map
`R_X -> M_N(F_2)`, with functions acting diagonally and `u` by the
cyclic permutation. It kills `u^N-1`, which is nonzero in the algebraic
crossed product by its direct-sum normal form. The induced group map
kills the nontrivial root `e_12(u^N-1)` but preserves the constant `c`.
Its kernel is again nontrivial and proper. These cases exhaust all
nonempty subshifts and prove the converse.

## 6. Scope and verification

The new content is the quantitative marked encoding and the exact
inclusion and simplicity correspondences. The prior Turing-degree
theorem already treated computability without these length bounds or
the topological and order statements. The Kazhdan and minimal-subshift
simplicity inputs remain the named existing graph claims. No global
priority assertion is made, and these written arguments are not Lean
formalizations.

The [finite-matrix receipt](pestov91-encoding-matrix-receipt-2026-09-13.json)
records an MSI check of the decoder, constant swaps, diagonal shift and
balanced recursion in dimension `21` over `F_2`, using the cyclic word
`0010111`. All `510` binary inputs of lengths `1` through `8` produced
exactly their expected cylinder matrices and met the word-length bound.
The run took `1.466` seconds in one Python 3.12 process. It evaluated
the expressions compositionally rather than expanding million-letter
strings. This finite check tests orientations and the length bookkeeping;
the arbitrary-subshift proof is the algebraic argument above.

The [Cairn receipt](pestov91-encoding-cairn-receipt-2026-09-13.json)
records successful check and preview on the archived research snapshot
at `1369b2bed03c273b0944a43029ef5f8c2c97c16a` with this change overlaid.
Cairn 2.13.1 parsed `10,236` claims and `10,495` routes, with no baseline
or final graph errors. Both new claims resolved as established. The
MSI run used one Python 3.12 process and took `33.825` seconds.

The runner replaced source and HEAD loading while retaining Cairn's
parser, lint, solver, check and preview policies. Artifact existence
used the exact tracked path manifest plus the delta; revision-pinned
artifacts used the warm repository's Git objects. This receipt and
paragraph were added afterward. These are graph checks, not Lean
verification of the mathematical proof.
