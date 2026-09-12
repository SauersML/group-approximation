# Normalized-HS-stable non-RF shortcut: exact current literature boundary

## The criterion

For a finitely presented group, normalized-HS stability plus non-residual
finiteness is already a nonhyperlinearity theorem.  Hyperlinear canonical
microstates would correct to separating finite-dimensional unitary
representations; Malcev then separates every nontrivial element in a finite
quotient.

The criterion can be weakened syntactically from global to **local** HS
stability.  Fournier-Facio--Gerasimova--Spaas,
arXiv:2307.13155v2, Lemma 3.11, prove for an arbitrary sequence of metric
groups that finite presentation makes local stability equivalent to global
stability.  Their statement explicitly includes the flexible and very
flexible variants.

Thus

```text
finitely presented + non-RF + locally normalized-HS stable
    ==> nonhyperlinear.                                   (A1)
```

## Why the published examples do not instantiate it

- Fournier-Facio--Gerasimova--Spaas construct non-RF groups which are locally
  HS-stable but not HS-stable.  Lemma 3.11 itself proves that these examples
  are not finitely presented.
- Dogon--Vidick, arXiv:2607.20135v1, prove polynomial normalized-HS stability
  for the lamplighter group.  It is residually finite and infinitely
  presented.
- Spaas, arXiv:2603.02058v1, proves HS stability for chordal graph products of
  abelian groups.  The finitely generated candidates are residually finite.
- De Chiffre--Glebsky--Lubotzky--Thom, arXiv:1711.10238, combine finite
  presentation, non-RF central extensions, and stability only for the
  unnormalized Frobenius norm.  Their cohomological engine requires a
  submultiplicative norm and does not give normalized-HS correction.
- Dogon--Vigdorovich, arXiv:2506.20843v2, obtain an explicit nonhyperlinear
  central extension only conditionally on flexible HS stability of
  `SL_2(Z[1/p])`; the Iwahori repair remains their stated open question.

## Marked weakening

Full stability is more than the contradiction consumes.  For a fixed word
in the finite-dimensional residual, it would suffice to correct canonical
trace microstates only far enough to make that word converge to its value in
an exact finite-dimensional representation.  None of the checked local,
hyperfinite, character-rigidity, or Frobenius results provides this marked
correction on arbitrary canonical microstates.

Exact finite-dimensional invisibility alone cannot replace it: the
Slofstra--Vidick finitely presented sofic example in
`exact-fd-invisibility-has-no-general-hs-robustification` has a nontrivial
central involution killed by every exact finite-dimensional representation
while its normalized-HS microstates keep the involution visible.

Therefore the direct literature shortcut remains open at one precise
intersection: finite presentation (or source-specific marked correction)
plus normalized-HS stability on a group with nontrivial finite residual.
