# Dimension-free partition rounding for self-adjoint Schur channels

Date: 2026-09-08. This is a self-contained finite-dimensional proof.
All matrix dimensions are arbitrary and all traces are normalized.

## 1. Statement and conventions

For `X in M_n(C)`, put

```text
||X||_2^2 = (1/n) Tr(X*X),
||T||_(infinity->2) = sup_(||X||_op<=1) ||T(X)||_2.
```

Let `S=(s_ij)` be a real positive semidefinite matrix with
`s_ii=1`, and define `P=P_S` by

```text
P(X)_ij = s_ij X_ij.
```

Then `P` is unital, completely positive, trace preserving, and
self-adjoint for the Hilbert--Schmidt inner product. Conversely,
every self-adjoint bistochastic UCP Schur map has this form.
Indeed, complete positivity is equivalent to positive
semidefiniteness of the Schur symbol: a Gram factorization gives
diagonal Kraus operators, and the Choi matrix restricted to the
span of `e_i tensor e_i` is `S`. Unitality fixes the diagonal
entries to one. The Hilbert--Schmidt adjoint has symbol
`conjugate(S)`, so self-adjointness makes the entries real.

Put

```text
delta = ||P^2-P||_(infinity->2).
```

**Theorem.** There is a partition `Pi` of `{1,...,n}` such that,
for the algebra and conditional expectation

```text
A_Pi = direct_sum_(B in Pi) M_B(C),
E_Pi(X) = sum_(B in Pi) p_B X p_B,
```

one has

```text
||P-E_Pi||_(infinity->2) <= min(1,4 sqrt(delta)).       (1)
```

More precisely, for every `0<t<1/10` there is such a partition
with

```text
||P-E_Pi||_(infinity->2)^2 <= 4t^2 + 2delta^2/t^2.     (2)
```

The partition in (2) may depend on `t`. Formula (1) requires
only one suitable partition, chosen below. The algebra remains
inside the original `M_n`; there is no padding or compression.

## 2. A matching detects the exceptional coordinates

Write

```text
d_ij = s_ij^2-s_ij.
```

The map `P^2-P` is the Schur multiplier with symbol `d_ij`.
Since `S` is a real correlation matrix,

```text
-1 <= s_ij <= 1,       s_ij=s_ji,       d_ii=0.
```

Fix `0<t<1/10`. On the coordinate set form a simple undirected
graph with an edge `{i,j}` precisely when `|d_ij|>t`.
Take a maximal matching, consisting of `r` disjoint edges,
and let `Z` be its `2r` endpoints. Let `U` be the permutation
matrix that exchanges the two endpoints of every matched edge
and fixes all unmatched vertices. This is a unitary, so

```text
delta^2 >= ||(P^2-P)(U)||_2^2
        = (1/n) sum_(matched {i,j}) (|d_ij|^2+|d_ji|^2)
        >= (2r/n)t^2.
```

The inequality is strict when `r>0`, but its weak form is what
we use. Thus

```text
|Z|/n <= delta^2/t^2.                                (3)
```

A maximal matching has a vertex cover among its endpoints:
an edge disjoint from `Z` could otherwise be added to the
matching. Therefore, for `Y={1,...,n}\Z`,

```text
|s_ij^2-s_ij| <= t       for all i,j in Y.             (4)
```

This step extracts control from the mixed norm directly. It
does not replace that norm by a bound on every entry of the
original matrix, which would incur a dimension factor.

## 3. Gram geometry makes the scalar split an equivalence relation

For `x in [-1,1]`, the following elementary estimates hold:

```text
x <= 1/2  ==>  |x| <= 2|x^2-x|,
x >= 1/2  ==>  |1-x| <= 2|x^2-x|.
```

Consequently each entry in (4) lies within `2t` of zero or one.
No entry in (4) equals `1/2`, since `t<1/10<1/4`.

On `Y` define `i ~ j` by `s_ij>=1/2`. This relation is
reflexive and symmetric. To prove transitivity, realize `S`
as the Gram matrix of real unit vectors `v_i`. If `i~j` and
`j~k`, then

```text
1-s_ij <= 2t,       1-s_jk <= 2t,
||v_i-v_j|| <= 2 sqrt(t),
||v_j-v_k|| <= 2 sqrt(t).
```

The triangle inequality gives

```text
2(1-s_ik) = ||v_i-v_k||^2 <= 16t,
so s_ik >= 1-8t.
```

If `i` and `k` were not related, the zero-side estimate would
give `s_ik<=|s_ik|<=2t`. This contradicts `1-8t>2t`, which
holds because `t<1/10`. Hence `~` is an equivalence relation.

Take its classes as blocks on `Y`, and add each member of `Z`
as its own singleton block. This defines a partition `Pi` of
all coordinates. Let

```text
e_ij = 1 if i,j belong to the same block of Pi, and 0 otherwise.
```

Then `E_Pi` is exactly the Schur multiplier with symbol `e`.
For `i,j in Y`,

```text
|s_ij-e_ij| <= 2t.                                  (5)
```

If an entry touches `Z`, its error is at most one: on the
diagonal both symbols equal one, while on every off-diagonal
entry touching `Z` the new symbol is zero and `|s_ij|<=1`.

## 4. Charge discarded rows and columns in the correct norm

Let `||X||_op<=1`. Each row and each column of `X` has squared
Euclidean norm at most one, and

```text
sum_(i,j) |X_ij|^2 <= n.
```

Split the squared output norm into entries in `Y x Y` and
entries touching `Z`. By (5),

```text
||(P-E_Pi)(X)||_2^2
 <= (4t^2/n) sum_(i,j in Y) |X_ij|^2
    +(1/n) sum_(i in Z or j in Z) |X_ij|^2
 <= 4t^2 + 2|Z|/n
 <= 4t^2 + 2delta^2/t^2.
```

The bound is uniform over the full operator-norm unit ball.
Taking its supremum proves (2).

If `0<delta<1/16`, set `t=sqrt(delta/7)`. This is less than
`1/10`, since `delta/7<1/112<1/100`. Formula (2) becomes

```text
||P-E_Pi||_(infinity->2)^2
 <= (4/7+14)delta
 = (102/7)delta
 < 16delta.
```

In this range `4 sqrt(delta)<1`, as required in (1).

For every `S`, the diagonal conditional expectation `E_D`
also satisfies

```text
||(P-E_D)(X)||_2^2
 = (1/n) sum_(i!=j) |s_ij|^2 |X_ij|^2
 <= ||X||_2^2 <= 1.
```

Use this partition when `delta>=1/16`. Finally, if `delta=0`,
testing individual matrix units gives `s_ij^2=s_ij` for all
entries. The real Gram vectors then satisfy `s_ij=1` exactly
when they coincide; the zero-one symbol is already a partition
symbol. Thus `P=E_Pi`, completing (1) in all cases.

## 5. Scope and source boundary

This theorem rules out a counterexample to dimension-free
conditional-expectation rounding **within the self-adjoint
Schur class**. It requires no nonnegative Hilbert-space
spectrum of `P`: real correlation symbols with negative entries
are included.

It does not show that an arbitrary self-adjoint bistochastic
UCP map can be put into Schur form by a basis change, nor that
native property-(T) microstate heat nearly fixes a maximal
abelian subalgebra. Those would be additional hypotheses or
additional theorems. No native heat-rounding conclusion, full
kernel feasibility result, or nonhyperlinearity theorem is
asserted here.

For context, exact idempotent Schur multipliers and their
combinatorial block structure are studied in Rupert H. Levene,
[Norms of idempotent Schur multipliers](https://arxiv.org/abs/1302.4849v2).
The present quantitative estimate is proved above and is not
imported from that paper. Alexei Kitaev's
[Almost-idempotent quantum channels and approximate C*-algebras](https://arxiv.org/abs/2405.02434v2)
uses completely bounded near-idempotence and obtains an
approximate factorization through an abstract finite-dimensional
C*-algebra. That is a different norm and conclusion from the
same-dimension mixed-norm conditional expectation in (1).
These primary sources and repository duplicates were checked
on 2026-09-08; no claim of priority is made.
