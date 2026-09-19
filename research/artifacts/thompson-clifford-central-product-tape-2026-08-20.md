# A finitely presented Thompson--Clifford central-product tape

Date: 2026-08-20.

## 1. The site action

Let `V=V_(2,1)` act by prefix replacements on the binary Cantor space and
fix the rational tail `xi=0^infinity`.  Let

```text
X=V.xi.
```

Equivalently, `X` is the countable set of binary sequences which are
eventually zero.  The action on `X` is faithful and highly transitive.
Indeed, for two ordered finite tuples of distinct points, choose pairwise
disjoint prefix cones around the source points and around the target points.
Prefix replacement on those cones sends the first tuple to the second; after
refining the two complementary finite prefix codes to the same cardinality,
the remaining cones can be paired arbitrarily.  The resulting finite prefix
table is an element of `V`.

In particular `V` has two orbits on `X x X`: the diagonal and the
off-diagonal.  The stabilizer `H=V_xi` is finitely generated (in fact of type
`F_infinity`).  The primary input is James Belk, James Hyde and Francesco
Matucci, *Stabilizers in Higman--Thompson groups*,
<https://arxiv.org/abs/2104.05572>, Theorem 1: stabilizers of finite nonempty
sets of rational Cantor points in `V_(n,r)` have type `F_infinity`.

## 2. Finite presentation

Let

```text
D=<p,q,j | p^2=q^2=j^2=1, j central, [p,q]=j>
```

be the order-eight dihedral/one-qubit Pauli group.  Form the permutational
wreath product

```text
W=(directSum_X D) semidirect V.
```

Yves de Cornulier, *Finitely presented wreath products and double coset
decompositions*, <https://arxiv.org/abs/math/0509090>, proves that a
permutational wreath product over a transitive action is finitely presented
exactly when the two groups are finitely presented, a point stabilizer is
finitely generated, and the diagonal action on `X^2` has finitely many
orbits.  All hypotheses hold here, so `W` is finitely presented.  The proof is
constructive from finite presentations of `D,V`, stabilizer generators, and
the two pair-orbit representatives.

Write `j_x` for the center of the copy at `x`.  Quotient `W` by the finitely
normally generated relations

```text
[j_xi,s]=1                 (s in one fixed finite generating set of V).
```

Transitivity identifies every `j_x` with one central involution `J`.  Denote
the quotient by `VCl`.  Its lamp kernel has the presentation

```text
K_X=<J,p_x,q_x (x in X) |
 J^2=p_x^2=q_x^2=1, J central,
 [p_x,q_x]=J,
 [p_x,p_y]=[q_x,q_y]=[p_x,q_y]=1 (x!=y)>.
```

Thus

```text
VCl=K_X semidirect V.                                      (TCP1)
```

No collapse is hidden in the quotient.  The central subgroup of
`directSum_X D` is the finitely supported `F_2`-space on `X`; imposing
`j_x=j_y` quotients it by the even-parity subspace and leaves one `C_2`.
The remaining Pauli normal form is unique.  Consequently

```text
1 -> <J> -> VCl -> ((directSum_X F_2^2) semidirect V) -> 1  (TCP2)
```

is a central extension with `J!=1`.

## 3. Binary self-similarity is a central product

Split `X=X_0 disjointUnion X_1` by the first binary digit.  The subgroup of
`V` supported on the cone `i{0,1}^infinity` is a copy `V_i` of `V`, and its
action on `X_i` is conjugate by prefix deletion to the original action on
`X`.  Put

```text
VCl_i=K_(X_i) semidirect V_i.
```

Each `VCl_i` is isomorphic to `VCl`.  The two subgroups commute and intersect
in the common center `<J>`, so

```text
<VCl_0,VCl_1>=VCl_0 *_(central <J>) VCl_1.                (TCP3)
```

The order-two prefix swap `0w <-> 1w` conjugates the two child groups.  This
is the nontrivial self-similar cocycle equation: the child centers are
*identified*, not multiplied.  It therefore avoids the false untwisted
identity `J=(J,J)`.  Restriction to either child remains non-split, witnessed
by `[p_x,q_x]=J`.

For a concrete nested qubit sequence choose

```text
x_n=0^n 1 0^infinity.
```

The pairs `(p_(x_n),q_(x_n))` commute across distinct levels and have common
commutator `J`.  Hence the first `n` pairs generate the rank-`n` extraspecial
Clifford group.  Standard prefix generators address `x_n` by a word of length
`O(n)`; conjugating the two base pair-orbit relators gives polynomial (indeed
linear apart from the fixed normal-form conversion) derivation cost.

## 4. Exact marked tracial model

On the infinite tensor product

```text
A=barTensor_(x in X) M_2(C)
```

with its product trace, represent `p_x,q_x` by the two Pauli matrices in the
`x`-th tensor factor and represent `J` by `-I`.  Different sites commute and
the same-site commutator is `-I`, so this is a faithful representation of
`K_X`.  The permutation action of `V` on `X` preserves the trace and extends
the representation to the crossed product `A crossed_product V`.  The action
on `X` is faithful, so `(TCP1)` is represented faithfully and `J` remains
`-I`.

This model proves exact marked completeness and exhibits one new CAR qubit at
every level.  It does not yet couple the tape to the non-CE BCS trace or prove
the finite-dimensional sibling-factor placement needed for the contraction
ledger; those are separate interfaces.
