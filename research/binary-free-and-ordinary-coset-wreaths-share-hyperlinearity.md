---
rg: 2
id: binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
kind: claim
title: Binary coset wreaths, amalgamated doubles, and centralizer HNN groups have equivalent hyperlinearity
distinct_from:
  binary-coset-lamp-coefficient-forces-relative-embedding: That extracts scalar relative embeddability from one CE binary coefficient; this adds the converse tensor Gaussian construction and identifies the approximation status of two different lamp groups.
  arithmetic-double-swap-extension-is-binary-coset-wreath: That identifies the free binary wreath with an index-two extension of the double; the ordinary binary wreath here has a commuting lamp kernel and is a different group.
  fd-fell-coset-observable-gaussianizes-wreath: That assumes genuine finite-image actor representations; this assumes only hyperlinearity of the free binary coset wreath and uses its CE tracial algebra in tensor powers.
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
  - research/artifacts/centralizer-hnn-relative-embedding-audit-2026-09-07.md
  - research/artifacts/coset-hyperlinearity-equivalence-literature-2026-09-07.md
---

For every inclusion `C<=A` of countable groups, the following are equivalent:

1. The ordinary binary coset wreath
   `W=(direct_sum_(A/C) C_2) rtimes A` is hyperlinear.
2. The free binary coset wreath
   `E=(*_(A/C) C_2) rtimes A=A *_C(C x C_2)` is hyperlinear.
3. The classical Gaussian crossed product
   `L^infinity(R^(A/C),gamma^(A/C)) rtimes A` is Connes embeddable.
4. The symmetric group double `D=A *_C A` is hyperlinear.
5. The centralizer HNN group `H=A *_C(C x Z)` is hyperlinear.
6. The inclusion `L(C)<=L(A)` is relatively embeddable over the scalar
   complex algebra.
7. The enlarged double `Dplus=(A x Z) *_C A` is hyperlinear.

The implication from `W` to `E` uses tensor amplification of the binary-lamp
conditional expectation to obtain scalar relative embeddability, followed
by the valid forward relative-amalgam theorem. The reverse implication
constructs new commuting Gaussian lamps from bounded tensor exponentials of
the free lamp involutions, with all canonical mixed actor moments verified.
Gaussian signs then give the ordinary binary lamps.

The free binary wreath is the factor-swap extension of the double, so
2 and 4 are equivalent by the explicit two-block construction. The lamp
coefficient gives 2 => 6; a scalar relative embedding gives the HNN model,
and rounding its Haar letter gives 6 => 5 => 2. The strengthened HNN
criterion also identifies 5, 6, and 7 directly.

These are equivalences of existence of canonical matrix models. The
constructions change the embedding and use tensor powers and larger
ultraproducts; they do not turn the commuting lamps in one fixed embedding
into free lamps within that same embedding.

No action-soficity assumption, exact actor correction, or general quotient
permanence is used. This equivalence does not decide whether these groups
are hyperlinear for any open arithmetic or Kun--Thom pair.
