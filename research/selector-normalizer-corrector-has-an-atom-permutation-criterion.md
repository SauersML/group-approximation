---
rg: 2
id: selector-normalizer-corrector-has-an-atom-permutation-criterion
kind: claim
title: A packet-normalizer corrector exists exactly when its atom permutation reverses the payload permutation
invalidates:
  - arbitrary-selector-normalizer-wordizes-stabilizer-corrector
distinct_from:
  selector-packet-central-corrector-fails-on-a-three-cycle: that rules out packet-central correctors by a three-cycle support argument; this allows the full selector-group normalizer and identifies exactly which permitted atom automorphisms repair the cycle structure.
  transitive-control-normalizer-forces-projectively-equal-payloads: that normalizes a full matrix control algebra and forces projective equality of payload blocks; this normalizes only a finite abelian selector group and shows that independent block gauges preserve arbitrary payload sensitivity whenever the finite permutation condition holds.
  extraspecial-fourier-zero-cell-is-fixed-face-pruning: that rules out the specific extraspecial shear normalizer through its fixed character face; this is the general block-monomial existence criterion before imposing that fixed-face deletion.
---

**ESTABLISHED.**  Let `X` be a finite selector-atom set and work on

```text
K=C^X tensor M,                    p_x=|e_x><e_x| tensor 1. (NCC1)
```

Let the payload be block monomial,

```text
W(e_x tensor xi)=e_(sigma x) tensor A_x xi,             (NCC2)
```

where `sigma in Sym(X)` and every `A_x` is an arbitrary unitary on `M`.
Fix a selected atom `x_0` with `sigma(x_0)!=x_0`, so `q=p_(x_0)` satisfies
`qWq=0`.  Let `A<=Sym(X)` be the atom-permutation image of the allowed
selector-group normalizer.  For a specified `alpha in A`, there is a
normalizer unitary `S` inducing `alpha` such that

```text
S q S^*=q,                    V=SW=V^*=V^-1              (NCC3)
```

if and only if

```text
alpha(x_0)=x_0,                    (alpha sigma)^2=1.     (NCC4)
```

Here `(NCC4)` is an exact finite algebraic criterion.  It is also the exact
ordinary-word criterion when `alpha` is prescribed by the finite conjugacy
relators for the stable letter `s` and `(sw)^2=1` is appended.

## Proof and payload freedom

Every normalizer inducing `alpha` has block-monomial form

```text
S(e_y tensor eta)=e_(alpha y) tensor S_y eta.            (NCC5)
```

Consequently the atom permutation of `SW` is
`tau=alpha sigma`.  Conditions `(NCC3)` force `alpha(x_0)=x_0` and
`tau^2=1`, proving necessity.

Conversely assume `(NCC4)`.  Choose arbitrary unitaries `B_x` along one
representative of each two-cycle of `tau`, put

```text
B_(tau x)=B_x^*,
```

and take `B_x=1` on every fixed point.  Define the block gauges of `S` by

```text
S_(sigma x)=B_x A_x^*.                                  (NCC6)
```

Then `S` induces `alpha`, while

```text
SW(e_x tensor xi)=e_(tau x) tensor B_x xi,
```

so `(SW)^2=1`.  Since `alpha` fixes `x_0` and `sigma(x_0)!=x_0`, injectivity
of `alpha` gives `tau(x_0)!=x_0`; hence `qSWq=0`.  Thus `(NCC3)` holds.

Crucially, `(NCC6)` works for **every** tuple `(A_x)`.  A selector-MASA or
finite abelian group normalizer has an independent unitary multiplicity
gauge on each atom, so the construction imposes no projective equality
between payload blocks.  Payload collapse occurs for a full matrix-algebra
normalizer, not here.  The only obstruction in this block-monomial setting
is the finite permutation condition `(NCC4)`.

## Exact four-character failure

Take the regular representation of `H=C_4`, whose four character atoms are
labelled by `X=Z/4`, and select `x_0=0`.  A unitary normalizing the represented
group `H` acts on characters through an automorphism of `C_4`; its only atom
permutations are

```text
alpha_+=id,                  alpha_-(j)=-j.              (NCC7)
```

Let `M=C` and let `W` have atom permutation

```text
sigma=(0 1 2),                       sigma(3)=3.          (NCC8)
```

Then `qWq=0`, but

```text
alpha_+ sigma=(0 1 2),
alpha_- sigma=(0 3 1 2).                                  (NCC9)
```

Neither permutation is an involution.  By `(NCC4)`, no selector-group
normalizer corrector can make `SW` involutive.  Nevertheless the unrestricted
selected-projection corrector from
`stabilizer-corrector-hermitianizes-zero-compression` still exists.

The distinction between normalizing the represented finite **group** and
normalizing its diagonal algebra is essential.  The latter allows every
permutation of `X` and can choose an `alpha` satisfying `(NCC4)` here; the
former allows only `(NCC7)`.  Thus a surviving wordization must either prove
the finite condition for its actual selector automorphism group, enlarge the
packet so the needed automorphism is genuinely available without introducing
unwanted types, or leave the packet normalizer.  This criterion does not
settle the remaining typewise payload-sensitive nontransport holonomy
readout outside the block-monomial face.
