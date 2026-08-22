---
rg: 2
id: hadamard-does-not-semidir-independent-selector-blocks
kind: claim
title: Hadamard transport cannot semidirectly wordize two independent selector blocks
distinct_from:
  hadamard-selector-commutator-charges-two-path-leakage: that positively charges the difference once a selector-central return word with the desired two blocks is given; this proves that the natural HNN, semidirect, and universal central-selector constructions cannot manufacture that input.
  britton-support-traps-dense-free-phase-chord: that uses HNN normal forms to trap the support of a completed group-algebra marginal; this is the two-block operator obstruction before any dense coefficient support is chosen.
  controlled-linear-predication-normal-form: that lowers already authenticated orthogonal controls; this proves why a literal group element with two independently prescribed controls cannot be supplied by a Hadamard semidirect action.
---

# Hadamard transport cannot semidirectly wordize two independent selector blocks

ESTABLISHED.  Let

```text
Z=diag(I,-I),             H=2^(-1/2)[ I  I ]
                                      [ I -I ]           (HSW1)
```

on `C^2 tensor M`.  For arbitrary operators `A,B` on `M`,

```text
H diag(A,B) H
 =1/2 [ A+B  A-B ].                                    (HSW2)
       [ A-B  A+B ]
```

Consequently

```text
H diag(A,B) H commutes with Z    iff    A=B.            (HSW3)
```

This elementary identity is the exact obstruction to the proposed
`G times G` wreath/semidirect wordization.  Suppose a subgroup `L` acts in
the selector centralizer, and a finite Hadamard packet letter `h` is required
by HNN or semidirect relations to carry `L` into another subgroup of that
same centralizer.  On the selected two-dimensional packet type, every
`ell in L` has form `diag(A_ell,B_ell)`, while `h ell h^-1` must again commute
with `Z`.  Formula `(HSW3)` forces

```text
A_ell=B_ell             for every ell in L.             (HSW4)
```

Thus the only selector-central subgroup normalized through the Hadamard
chart is the diagonal multiplicity subgroup `I_2 tensor U(M)`.  It has
already identified the two paths; it cannot first carry independent `A,B`
and then let the leakage relator compare them.

The obstruction also has a purely group-algebra form for a central
selector.  Let `z` be a nontrivial central involution in a group `Gamma`, put
`p_+=(1+z)/2`, `p_-=(1-z)/2`, and let `a,b,d in Gamma` commute with `z`.  If
one asks a single group element to have universally prescribed blocks

```text
p_+ d p_+=p_+ a p_+,       p_- d p_-=p_- b p_-,         (HSW5)
```

then linear independence of the group basis gives

```text
d in {a,za},              d in {b,zb}.                  (HSW6)
```

Indeed `(1+z)d=(1+z)a` says exactly that the two-element cosets
`{d,zd}` and `{a,za}` agree, and similarly for the negative equation.
Therefore

```text
a^(-1)b in <z>.                                        (HSW7)
```

Independent group-word paths cannot be assembled by a universal central
spectral selector; only a central-sign difference is possible.

There are now only two cases for the natural wreath construction.

1. **Make Hadamard transport an HNN/semidirect automorphism.**  Then
   `(HSW3)` forces equal blocks before the new commutator is applied.
2. **Adjoin the Hadamard packet freely relative to `G times G`.**  A literal
   base element `(a,b)` exists, but arbitrary representations need not put
   the first base factor only on the `Z=+1` line and the second only on the
   `Z=-1` line.  Those type-filtered support conditions are exactly the
   corner equations `(HSW5)`, not consequences of the group product.

Hence neither a graph-of-groups extension nor a semidirect product supplies
the diagonal return required by
`hadamard-selector-commutator-charges-two-path-leakage`.  A successful cell
must use a genuinely non-normalizing finite-packet compression whose two
block coefficients are forced simultaneously, or solve the additive
signed-Hecke corner equality directly.  Controlled predication and termwise
finite-edge transport do not cross this boundary.

