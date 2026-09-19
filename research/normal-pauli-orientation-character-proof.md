---
rg: 2
id: normal-pauli-orientation-character-proof
kind: route
title: Compose the orthogonal outer action with the product sign of the two rulings
target: normal-pauli-extensions-retain-the-orientation-character
requires:
  - orientation-graded-mixed-returns-have-a-balanced-double
---

The quotient `P/Z(P)` is a four-dimensional vector space over `F_2`.  If an
element is written `(a_1,a_2;b_1,b_2)`, its square defines the plus-type
quadratic form

```text
q(a,b)=a_1 b_1+a_2 b_2.
```

Automorphisms fixing `J` preserve both commutators and element squares, so
modulo inner automorphisms one obtains

```text
Out_J(P)=O_4^+(F_2)~=(S_3 x S_3) semidirect C_2.
```

For a concrete check identify `(a,b)` with

```text
M(a,b)=[[a_1,a_2],[b_2,b_1]],       det M=q(a,b).
```

The two `S_3=GL_2(F_2)` factors act by left and right multiplication, and
the final `C_2` swaps the two rulings by transpose.  Controlled-Z sends

```text
(a_1,a_2;b_1,b_2)
 ->(a_1,a_2;b_1+a_2,b_2+a_1),
```

which is left multiplication of `M` by `[[1,0],[1,1]]`, a transposition in
the first `S_3`, and is the identity in the second factor.  The character

```text
(g_1,g_2) -> sgn(g_1)sgn(g_2)
```

is invariant under swapping the factors, so it extends over the semidirect
product and takes controlled-Z to `-1`.  Because `P` is normal in `Gamma`
and `J` is central, conjugation followed by this character proves `(NPO2)`.
Inner automorphisms have trivial outer class, proving the asserted value on
`P`.

The balanced-double conclusion is then exactly
`orientation-graded-mixed-returns-have-a-balanced-double`.  Since the
character was constructed from the normal packet action itself, adjoining
further packet normalizers cannot remove it.
