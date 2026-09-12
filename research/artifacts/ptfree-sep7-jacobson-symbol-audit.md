# The finite Jacobson packet is not finitary

Date checked: 2026-09-07.

This is a correction to a proof on the intrinsic Property-(T)-free MF
frontier, not a non-MF theorem or a literature novelty claim. The calculation
is internal to the exact coefficient rings and uses no executable experiment.

The route `binary-jacobson-joint-shortest-cells-finite-model-proof` places
the finite packet `F=EL_3(F_2[Q])` and the balanced involution `h` inside
the LEF group `H=<L,a>`, where `L` is the finitary kernel and `a` is one
Whitehead translation. It asserts that every element of `F` differs from
the identity on only a finite coordinate packet, and that the constant
Weyl swap `u=w_12(1)` belongs to `L`. The finite cardinality of the group
`F` does not imply finite support in the Jacobson module. Both assertions
are false.

Use the standard basis `e_0,e_1,...` on each coordinate ray. Here

```text
Q e_0=e_0,           Q e_n=0 for n>=1,
(1-Q)e_0=0,         (1-Q)e_n=e_n for n>=1.
```

Thus a head element `g_Q` acts on the three vectors at level zero and is
finitary. A tail element `g_P` repeats its same three-dimensional action
at every level `n>=1`. A constant element is the diagonal pair `(g,g)`;
it repeats its action at every level, including zero. In particular the
constant swap exchanges the first two rays at infinitely many levels.

Equivalently, the Laurent symbol

```text
sigma(S)=z,       sigma(T)=z^(-1),       sigma(Q)=0
```

is the projection from `G_Q x G_P` onto its tail factor. Its kernel on
the packet is exactly `G_Q`, whereas its image is the entire constant
`EL_3(F_2)`.

The balanced matrices satisfy

```text
a=[[S,Q,0],[0,T,0],[0,0,1]],
h=a u=[[Q,S,0],[T,0,0],[0,0,1]],
sigma(a)=diag(z,z^(-1),1),
sigma(h)=[[0,z,0],[z^(-1),0,0],[0,0,1]].
```

The image of `H=<L,a>` is cyclic and diagonal. The image of `h` is
nondiagonal. This directly disproves the asserted containment even without
using generation of the full elementary group.

Adjoining the constant packet to `L` does not repair this LEF argument
after `a` is added. The established active-cycle calculation extracts all
`S`, `T`, and `Q` roots from `a` and the constant elementary roots, so

```text
<F,h>=EL_3(J).
```

The claimed subsystem inclusion would therefore place the whole active
Jacobson group inside a subgroup with cyclic symbol, even though its actual
symbol is `EL_3(F_2[z,z^(-1)])`. The existing LEF theorem controls only
one cyclic symbol direction.

The exact scope of the correction matters. It revokes the available proof
that the two shortest cells jointly admit an exact finite marked model.
It does not prove that their joint quotient has no such model, and does not
invalidate the individually established models for either cell separately.
The full Property-(T)-free radical theorem remains open. In Cairn the
correction is therefore a source-owned invalidation of the erroneous route,
not a `refuted_by` link on its target claim.

The current external status was checked separately against the primary
abstract of Caleb Eckhardt's [Non-MF groups and non-finite full group
C*-algebras](https://arxiv.org/abs/2608.28772), dated August 28, 2026. Its
non-MF construction explicitly starts with a Property-(T) group, so it does
not independently close the present Property-(T)-free endpoint. That
literature fact is not used in the symbol proof.
