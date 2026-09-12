---
rg: 2
id: affine-whitehead-stability-hypothesis-audit
kind: route
title: Check every available stability theorem against the affine Whitehead and wagon-wheel hypotheses
target: affine-whitehead-hyperfinite-stability-misses-canonical-mark
requires:
  - full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark
  - slofstra-solution-group-embedding-preserves-marked-involutions
  - marked-approximate-radical-survives-solution-group-embedding
  - hs-stability-descends-to-retracts
  - fournier-facio-universal-frobenius-stable-t-embedding
  - exact-fd-invisibility-has-no-general-hs-robustification
---

The positive part is a direct application of the primary source.  The
one-relator quotient `Gamma_A'` retains property `(T)`.  Every von Neumann
amenable factorial representation of a Kazhdan group is finite-dimensional,
so every amenable character is a pointwise limit of finite-dimensional
traces.  Dogon--Vigdorovich Theorem 6.2 corrects every hyperfinite asymptotic
representation in the same dimension.  Exact finite-dimensional collapse
then kills `W`; the fixed finite amalgam and Clifford relations kill `J`.

For the boundary, a canonical approximation converges in moments to the
regular marked von Neumann algebra.  Since the affine vertex is infinite
Kazhdan it is nonamenable, so this marked algebra is not hyperfinite.  The
only applicable positive theorem has therefore excluded the target sequence
in its definition.

The remaining rows are hypothesis checks, not analogies: strict/flexible
normalized-HS stability is unproved and would itself contradict a canonical
approximation; Frobenius stability is unnormalized; character rigidity
assumes a commutative Noetherian coefficient ring; Slofstra gives an
embedding but supplies no retract or approximate extension functor; and the
universal stable host theorem again uses Frobenius norm.  The cited generic
counterexample to robustifying exact finite-dimensional invisibility shows
that no omitted formal implication can bridge the gap.

The character and normal-subgroup audit is stronger than a theorem-hypothesis
check.  Centralizing the active coefficient head and projecting either of its
two Wedderburn blocks gives

```text
Gamma_A' -> EL_5(M_3(L_2(k))) times EL_5(M_3(L_2(k))).
```

The Whitehead fourth-power relator dies in this elementary quotient.  Either
coordinate map has infinite kernel, and the elementary factor modulo center
is infinite simple by the exchange-ring normal-subgroup theorem.  Pullback of
its regular character is factorial, nonregular on `Gamma_A'`, and not finite
dimensional.  Thus regular-or-finite-dimensional character rigidity is false
for the actual affine group, while a CE-only replacement would already have
to settle the ordinary Leavitt factor's hyperlinearity.  Passing to the active
finite-index factor or through the `W^4` correction does not remove this
quotient face.  The more general Lavi--Levit conclusion is not contradicted:
the quotient-regular character is induced from the trivial representation of
its kernel.  Precisely for that reason, even that conclusion would not make
the character hyperfinite.

Primary sources checked:

- A. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*, arXiv:2506.20843v2, Definition 6.1,
  Theorem 6.2, Corollary 7.7, and Theorem 7.10.
- O. Becker and A. Lubotzky, *Group stability and Property (T)*,
  arXiv:1809.00632, Theorem 1.3(ii).
- M. De Chiffre, L. Glebsky, A. Lubotzky and A. Thom, *Stability,
  cohomology vanishing, and non-approximable groups*, arXiv:1711.10238,
  Theorems 1.2 and 3.6.
- O. Lavi and A. Levit, *Characters of the group `EL_d(R)` for a commutative
  Noetherian ring `R`*, arXiv:2007.15547, Corollary 1.3.
- W. Slofstra, *Tsirelson's problem and an embedding theorem for groups
  arising from non-local games*, arXiv:1606.03140, Theorem 3.1 (the marked
  wagon-wheel embedding theorem in the published numbering).
