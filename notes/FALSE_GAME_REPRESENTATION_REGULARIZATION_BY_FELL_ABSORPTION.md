# Fell absorption erases a game representation under regularization

Date: 2026-08-14

## 1. Outcome

Suppose a finitely presented game algebra has a tracial representation

```text
pi:G -> U(M)
```

inside a finite von Neumann algebra, and suppose one tries to force the
canonical group trace by tensoring the generators with the left regular
representation:

```text
rho(g)=pi(g) tensor lambda_G(g).                       (FAR1)
```

The trace of `(FAR1)` is indeed the regular character.  This does **not**
implant `M` into a group factor.  Fell absorption gives an explicit unitary
which removes `pi` from the generated representation:

```text
rho ~= 1 tensor lambda_G.                              (FAR2)
```

Consequently

```text
W*(rho(G)) ~= L(G),                                   (FAR3)
```

independently of whether `M` is Connes embeddable.  A non-CE perfect-game
representation therefore cannot be converted into a nonhyperlinear group by
this regular-tensor trick.  The construction proves nothing about the
Connes embeddability of `L(G)` that was not already true before `pi` was
introduced.

This is an exact obstruction.  It uses no approximation, dimension bound, or
stability assumption.

## 2. Explicit absorption unitary

Let `G` be countable and let `pi:G->U(K)` be any unitary representation.
On `K tensor ell2(G)` define

```text
W(xi tensor delta_h)=pi(h^(-1))xi tensor delta_h.       (FAR4)
```

This is unitary, with

```text
W*(xi tensor delta_h)=pi(h)xi tensor delta_h.           (FAR5)
```

For `g,h in G`, direct calculation gives

```text
W (pi(g) tensor lambda(g)) W*(xi tensor delta_h)
 =W(pi(g)pi(h)xi tensor delta_(gh))
 =pi((gh)^(-1))pi(g)pi(h)xi tensor delta_(gh)
 =xi tensor delta_(gh).                                (FAR6)
```

Thus

```text
W (pi(g) tensor lambda(g)) W*=1 tensor lambda(g)       (FAR7)
```

for every `g`, proving `(FAR2)--(FAR3)`.

The same calculation works when `pi(g)` lies in a finite von Neumann algebra
`M`: represent `M` faithfully on `K` and apply `(FAR4)` fiberwise.  The
absorbing unitary may lie in the ambient `B(K tensor ell2(G))`; it need not
belong to the diagonal group algebra.  Spatial equivalence of the generated
von Neumann algebras is all that is needed for `(FAR3)`.

## 3. Why the character calculation is misleading

If `M` has trace `tau` and the tensor product is equipped with
`tau tensor tau_G`, then

```text
(tau tensor tau_G)(rho(g))
 =tau(pi(g)) tau_G(lambda(g))
 =0                         when g!=1,                 (FAR8)
```

and the value at the identity is one.  Hence the diagonal representation
has the canonical regular character even when `pi` has a highly nonregular
or non-CE character.

Equation `(FAR8)` can look like a trace-selection mechanism: it kills all
unwanted Fourier coefficients.  Equation `(FAR7)` shows what actually
happens.  The same regular factor which kills those coefficients also absorbs
the entire representation carrying the desired obstruction.  The group
generators retain no recoverable copy of `M`.

This explains why taking a non-CE game representation, tensoring it with a
regular group representation, and then invoking the canonical trace cannot
solve the universal-hyperlinearity problem.

## 4. Corners and Hecke representations are a different problem

A quasi-regular or induced representation can retain stabilizer data, and a
finite-subgroup idempotent may produce a Hecke corner.  But this no longer
has the form `(FAR1)`, and two additional requirements become load bearing:

1. the corner must sit in the **canonical** group von Neumann algebra, not
   merely in an arbitrary representation of the group; and
2. the corner trace must agree with the desired game trace and the corner
   must contain the game algebra as a normal trace-preserving subalgebra.

Merely producing a representation or a weak-containment map does not meet
either requirement.  If a non-CE finite algebra were actually embedded as a
nonzero corner of `L(G)`, then `L(G)` would be non-CE and `G` would be
nonhyperlinear.  Constructing such a corner is therefore essentially the
group-factor groupification problem itself, not a consequence of induction.

For finite local constraint subgroups there is a further obstruction:
`FALSE_LOCAL_BCS_SPECTRAL_EXCLUSION_BY_GROUP_RELATIONS.md` proves that the
regular representation restores every compatible local character.  Thus a
finite Hecke or truth-table gadget cannot delete precisely the forbidden
nonaffine Boolean atoms.

## 5. Consequence for the perfect-game lane

The negative solution of Connes embedding supplies finite games with a
perfect commuting-operator strategy and a finite-dimensional gap.  To obtain
a nonhyperlinear group from such a game one still needs a compiler which
retains the non-CE trace inside the **regular** group character.  Fell
regularization cannot be that compiler:

```text
non-CE game representation
  + diagonal regular tensor
  = regular group representation, with the game sector absorbed.  (FAR9)
```

The live alternatives remain:

- a one-instance perfect BCS-to-LCS compiler with robust reverse decoding;
- a genuine canonical Hecke/group-factor corner theorem; or
- one of the independent matrix-coordinate radical-collision endpoints.

The second alternative must do more than regularize an arbitrary
representation; `(FAR7)` proves that such regularization is sterile.

## Relation to existing notes

The fiberwise unitary `(FAR4)` already appeared inside the origin-absorption
discussion in `NOTEPAD.md`, where it was used to show that a strict operator
is relocated into a multiplicity cocycle.  The present note isolates the
complementary generated-algebra consequence needed for game groupification:
if only the diagonal group generators are retained, their von Neumann algebra
is spatially just `L(G)` and the auxiliary representation disappears.

`FALSE_SEMIFINITE_MORITA_COMPRESSION_NO_GO.md` proves an analogous
cancellation for a quasi-regular wall passed through an inner crossed product
and a finite Morita corner.  Together, the two results rule out both direct
regular tensoring and its most immediate semifinite-corner variant.

