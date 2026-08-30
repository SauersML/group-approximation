# STW Problem XCI: locally finite permutation wreath audit

## Result

For every nontrivial countable linear group `P` with trivial amenable
radical and every countable locally finite permutation group
`L <= Sym(X)`, the generalized wreath product

```text
P^(X) rtimes L
```

has selfless reduced C-star algebra.  The top action may have infinite
support.  Regular actions of infinite locally finite groups give explicit
new examples not covered by the finitary-permutation theorem.

## Packet audit

Local finiteness, rather than finite support, makes every finitely generated
top subgroup `K` finite.  Faithfulness of `K` on all of `X` has a finite
witness: choose one moved point for each nonidentity element and close the
finite set under `K`.  After adjoining the finite orbit of any prescribed
lamp support, this yields a finite invariant set `S` on which `K` acts
faithfully.  These pairs are directed and exhaust the full wreath product.

The block-monomial representation of `P^S rtimes K` is faithful.  Its
amenable radical is trivial: intersection with `P^S` dies coordinatewise,
normality then forces the remaining radical to centralize `P^S`, and a
nontrivial permutation cannot centralize a lamp supported at a moved
coordinate.  Faithfulness on `S` removes the only possible kernel.

Vigdorovich therefore applies to every finite packet, and Robert's
directed-union theorem applies to their canonical trace-preserving reduced
group-algebra inclusions.  No permanence of C-star simplicity under finite
extensions is assumed.

## Boundary

The proof requires local finiteness of `L`.  For a merely amenable or
residually finite permutation group, a finitely generated top subgroup need
not be finite, so the packets need not be linear or fall under the imported
linear selflessness theorem.  The result advances the positive group class
for XCI but does not prove the universal C-star-simple-group statement.
