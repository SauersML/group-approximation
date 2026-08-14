# Four-root associativity has a table-size-independent HS budget

Date: 2026-08-14

## 1. Outcome

The second coproduct defect in the multiplicative-unitary route does not
suffer a cardinality loss from the growing coefficient table.  Ring
associativity is represented by one bounded Steinberg word on four ordered
root indices:

```text
[[x_12(a),x_23(b)],x_34(c)]
 =x_14((ab)c)
 =x_14(a(bc))
 =[x_12(a),[x_23(b),x_34(c)]].                       (FRA1)
```

If a unitary microstate has multiplicative error at most `delta` on the
finite packet containing these elements and their partial products, the two
evaluated sides of `(FRA1)` are at normalized-Hilbert--Schmidt distance at
most

```text
30 delta.                                             (FRA2)
```

The constant is independent of the matrix dimension and of the number of
coefficient triples.  Consequently the normalized mean squared
associativity defect over any finite table is at most

```text
900 delta^2.                                          (FRA3)
```

This closes a possible quantitative escape in the approximate
bi-corepresentation program.  The live gap is the construction of its one
coefficient unitary `V`, not accumulation over the multiplication table.

## 2. Exact four-root identity

For distinct ordered indices `1<2<3<4`, the Steinberg relations give

```text
[x_12(a),x_23(b)] = x_13(ab),
[x_13(ab),x_34(c)] = x_14((ab)c),                    (FRA4)
```

and

```text
[x_23(b),x_34(c)] = x_24(bc),
[x_12(a),x_24(bc)] = x_14(a(bc)).                    (FRA5)
```

Associativity in the coefficient ring identifies the two central root
elements.  No Hall--Witt approximation or choice of parenthesization is
needed: both nested commutators are literally the same group element.

The finite envelope in
`TRUE_FINITE_UNITRIANGULAR_MULTIPLICATION_ENVELOPE.md` contains every
element in `(FRA4)--(FRA5)` simultaneously.

## 3. The universal `30 delta` telescope

Let `phi` map the relevant finite group packet to unitaries, with

```text
phi(1)=1,
||phi(gh)-phi(g)phi(h)||_2 <= delta                    (FRA6)
```

whenever the displayed product is used.  Unitary invariance gives

```text
||phi(g^-1)-phi(g)*||_2 <= delta.                     (FRA7)
```

A four-letter commutator therefore satisfies

```text
||[phi(g),phi(h)]-phi([g,h])||_2 <=5 delta.           (FRA8)
```

There are three multiplication telescopes and two inverse replacements.

The unitary commutator is `2`-Lipschitz in either unitary argument:

```text
||[U,V]-[U',V]||_2 <=2||U-U'||_2.                    (FRA9)
```

Apply `(FRA8)` first to the inner commutator.  Replacing that inner value in
the outer commutator costs at most `10 delta` by `(FRA9)`, and applying
`(FRA8)` to the outer commutator costs another `5 delta`.  Each nested path
in `(FRA1)` is consequently within `15 delta` of the common root image
`phi(x_14(abc))`.  The triangle inequality gives `(FRA2)`.

The estimate deliberately uses a safe universal constant.  Optimizing it
has no mathematical value because hyperlinearity lets the packet tolerance
be chosen after the finite coefficient table is fixed.

## 4. Normalized aggregation

Let `A,B,C` be arbitrary nonempty finite coefficient sets and denote the
two nested-commutator evaluations by `L_(a,b,c)` and `R_(a,b,c)`.  Squaring
`(FRA2)` and averaging gives

```text
(1/(|A||B||C|))
  sum_(a,b,c) ||L_(a,b,c)-R_(a,b,c)||_2^2
 <=900 delta^2.                                       (FRA10)
```

There is no union bound.  This is the normalization required by the
coefficient Parseval identity in
`TRUE_APPROXIMATE_BICOREPRESENTATION_CLASSICALIZATION.md`.

Thus a diagonal sequence may let `|A|,|B|,|C|` grow arbitrarily while
choosing `delta->0`; the total associativity energy still tends to zero.

## 5. Exact remaining interface

Equation `(FRA10)` supplies the multiplication-coherence estimate **after**
the four-index coefficient blocks have been assembled into one unitary

```text
V in Ahat tensor M_d tensor A.                        (FRA11)
```

It does not construct `(FRA11)`.  The missing theorem must identify the
raw/comb block coefficients in the single repaired unitriangular envelope
and prove that they are the coefficients of one unitary (or one asymptotically
unitary corner).  Once that is done:

```text
four-root associativity
 -> delta_R -> 0 by (FRA10),
additive root exactification
 -> delta_L -> 0,
approximate bi-corepresentation
 -> averaged coefficient commutation,
whole-map decoder
 -> robust 1/36 contradiction.                       (FRA12)
```

The source of difficulty is therefore a single completeness/unitarity
identity for the coefficient blocks.  It is not multiplication-table size,
associativity error, or Pauli gauge matching.

No local computation or build was run for this note.
