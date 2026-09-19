---
rg: 2
id: jnvwy-padded-succinct-clauses-force-proof-atom-booleanity-proof
kind: route
title: Use the equality and unit-clause families as an exact Booleanity test
target: jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes
requires:
  - jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms
---

Work in Ji--Natarajan--Vidick--Wright--Yuen,
arXiv:2001.04383v3.  The labels below refer to that version.  By
`jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms`, a nonzero
perfect proof atom is a literal low-individual-degree proof

```text
Pi=(g_1,...,g_5,c_0,...,c_m')
```

in the sense of Definition 10.23 and its PCP view is accepted at every point.
The Formula and Zero-on-Subcube tests in Figure 13 therefore give the
polynomial identities

```text
c_0(z)=phi_arith(z) product_(i=1)^5 (g_i(x_i)-o_i),    (PCB1)
c_0(z)=sum_(j=1)^m' c_j(z) z_j(1-z_j).                (PCB2)
```

These are the two identities used in the soundness proof of Theorem 10.25,
immediately before its Boolean decoding step.

## Every selected clause is satisfied over the field

Restrict `(PCB2)` to the Boolean cube.  Its right side vanishes, so
`c_0(z)=0`.  Fix indices `i_1,...,i_5` and polarities
`o_1,...,o_5` for which the succinct circuit selects the corresponding
decoupled clause.  By the Tseitin property recalled in the proof of
Theorem 10.25, there is a Boolean internal-wire string `w` with
`phi(x,o,w)=1`; its arithmetization has the same value on the Boolean cube.
Substitute this `w` and the binary encodings of the five indices in `(PCB1)`.
Since the coefficient is one and the ground ring is a field,

```text
there is an r in {1,...,5} with g_r(i_r)=o_r.          (PCB3)
```

Here and below `g_r(i)` abbreviates evaluation at the binary encoding of
`i`.  Thus every circuit-selected clause is satisfied even when the five
tables are initially regarded as field-valued assignments.

## The unpadded circuit forces the first two blocks to be Boolean

In the proof of Proposition 10.18 (Explicit succinct descriptions), the
succinct circuit includes all clauses selected by either of the conditions

```text
i_1<2T,  i_1=i_3,      o_1 != o_3,                    (PCB4)
i_2<2T,  i_2=i_3-2T,   o_2 != o_3.                    (PCB5)
```

The remaining indices and polarities are unrestricted.  Suppose, for
contradiction, that `g_1(i_1)=theta` is outside `{0,1}` for some `i_1<2T`.
Set `i_3=i_1`.  Choose `o_3` unequal to `g_3(i_3)`; this is always possible
because `o_3` has two choices.  Set `o_1=1-o_3`.  Then `theta` is unequal to
`o_1`.  Choose arbitrary remaining indices and, independently for each of
their field values, choose its Boolean polarity unequal to that value.
Condition `(PCB4)` selects this clause, but none of its five equalities in
`(PCB3)` holds, a contradiction.  Hence `g_1(i_1)` is Boolean.

The same argument with `i_3=i_2+2T` and `(PCB5)` proves Booleanity of
`g_2(i_2)` for `i_2<2T`.

For the remaining coordinates of the two original blocks, the same circuit
contains the four unit-clause families

```text
i_1>=2T and i_1 odd  and o_1=1,
i_1>=2T and i_1 even and o_1=0,
i_2>=2T and i_2 odd  and o_2=1,
i_2>=2T and i_2 even and o_2=0.                        (PCB6)
```

Again all other polarities are unrestricted.  If the selected `g_1` or
`g_2` value were non-Boolean, choose every other polarity unequal to its
field value.  The resulting selected clause would violate `(PCB3)`.
Indeed `(PCB6)` forces the precise alternating tape-symbol padding, not just
Booleanity.

## The outer padding preserves the Booleanity test

Proposition 10.19 (Padding) enlarges the first two blocks from lengths `L`
to `L'` by adding exactly the same four unit-clause families for every new
coordinate `i_1>=L` or `i_2>=L`; see its displayed five-condition definition
of the padded circuit.  Applying the preceding argument to these new
coordinates proves `(PBC2)` on all `M=2^m` Boolean-cube positions.

Finally, JNVWY's decoding definition in Section 3.3 says

```text
Dec_{0,1}(g)_y = g(y) if g(y) in {0,1}, and 0 otherwise.
```

Consequently `(PBC2)` gives `(PBC3)`.  Since restriction and polynomial
addition are linear and the field has characteristic two, for any odd list
of positive atoms,

```text
Dec(sum_j g_i^(j))=xor_j Dec(g_i^(j)),  i=1,2,         (PCB7)
```

provided the summed proof is everywhere accepted (the situation obtained
when every output question support is affine-safe).  Off-Boolean-cube
modifications such as `x_j(1-x_j)` remain possible, but they do not affect
`(PCB7)`.
