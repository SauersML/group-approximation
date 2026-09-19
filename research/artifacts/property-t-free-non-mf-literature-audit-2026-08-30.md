# Property-(T)-free non-MF literature audit (2026-08-30)

## Result of the search

The search found no public primary source supplying an unconditional
property-`(T)`-free construction of a weak/CDE non-MF group.  The current
manuscript has an unconditional non-MF group, but its proof cone uses
Kazhdan rigidity; this audit concerns a replacement proof whose full
provenance avoids Property `(T)`.

Bachner--Dogon--Lubotzky,
[*On L1-approximation of groups*](https://arxiv.org/abs/2508.17392),
arXiv:2508.17392v3, still calls the operator-norm MF problem open in its
April 2026 revision.  Its Proposition 2.4 is nevertheless exactly the
property-`(T)`-free matrix tool needed here: an asymptotically invariant
nonzero projection can be compressed and polar-corrected to an asymptotic
representation on its range.  The in-repository theorem
`mf-finite-normal-tracially-visible` strengthens this for a finite normal
subgroup by summing an isotypic orbit to make the projection invariant and
then taking the corner's intrinsic normalized trace.

This produces the following closed implication:

```text
finite LCS with omega^co=1>omega^q
  => central solution-group sign J is algebraically nontrivial
  => a weak MF embedding makes J HS-visible on an invariant sign corner
  => Slofstra--Vidick gives omega^q=1
  => contradiction.
```

The conclusion rules out the repository's weak operator-norm MF notion,
not merely a trace-sensitive strengthening.  No hyperlinearity implication
is smuggled into the proof.

## Definition firewall

For the weak convention, a faithful norm-corona homomorphism can become
nonfaithful after passing to normalized-Hilbert--Schmidt norm: separation
may live on `o(d_n)` dimensions.  Korchagin,
[*MF-property for countable discrete groups*](https://arxiv.org/abs/1704.06906),
explicitly records that weak MF does not automatically imply
hyperlinearity.  Thus the already established theorem
`perfect-lcs-gap-implies-nonhyperlinear` cannot simply be relabelled as a
weak non-MF theorem.  The invariant finite-sign corner is the additional
argument which removes the vanishing-rank escape.

## Exact upstream gap

Paddock--Slofstra,
[*Satisfiability problems and algebras of boolean constraint system games*](https://arxiv.org/abs/2310.07901),
Lemma 5.7 identifies tracial and `R^U` satisfiability of an LCS with,
respectively, algebraic and approximate visibility of its central solution-
group involution.  Their Proposition 5.8 says that a tracially satisfiable
but non-`R^U`-satisfiable LIN system exists if and only if a finitely
presented nonhyperlinear group exists.  Therefore importing a general BCS
gap from `MIP*=RE` and silently converting it to LIN would assume the main
missing theorem.

Taller--Vidick,
[*Approximating the quantum value of an LCS game is RE-hard*](https://arxiv.org/abs/2507.22444),
arXiv:2507.22444v2, prove LCS hardness with completeness `1-epsilon` and
state explicitly that `epsilon=0` would imply a nonhyperlinear group.  They
also explain the algebraic obstruction to a generic BCS-to-LCS
`*`-morphism.  Hence their imperfect completeness cannot be rounded away in
the present argument.

The July 2026 paper of Cleve--Culf--Taller,
[*XOR Games at Full Tilt*](https://arxiv.org/abs/2607.06876), does not close
this boundary.  Its tilted-XOR hardness is centered at value `3/4`, and the
paper notes that ordinary binary games have a perfect quantum strategy if
and only if they have a perfect classical one.  It supplies neither a
perfect commuting LCS gap nor the missing BCS-to-group compiler.

## Recent papers not previously incorporated

The arXiv search through 2026-08-30 also checked the following recent
directions.

* Brannan--Matsuda--Seguin,
  [*Representation stability for compact and discrete quantum groups*](https://arxiv.org/abs/2608.26362),
  proves uniform operator-norm Ulam stability for compact quantum groups
  and amenable discrete quantum groups.  This is genuinely property-`(T)`-
  free, but a weak MF sequence has only pointwise defect convergence; its
  bad multiplication pair may move with the coordinate.  Uniform Ulam
  stability therefore does not round the required pointwise models.
* Moravec,
  [*Polynomial permutation stability, soficity, and universal polynomial groups*](https://arxiv.org/abs/2608.21817),
  concerns permutation/Hamming approximation and supplies no operator-norm
  obstruction.
* Manzoor,
  [*There Is An Equivalence Relation Whose von Neumann Algebra Is Not Connes Embeddable*](https://arxiv.org/abs/2502.06697),
  constructs a non-cohyperlinear invariant random subgroup and a non-CE
  equivalence relation.  The IRS need not be a point mass, so it does not
  produce a nonhyperlinear group or a central sign killed in all group
  microstates.
* Kun--Thom,
  [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
  and Fournier-Facio,
  [*A torsion-free non-sofic group*](https://arxiv.org/abs/2608.02025),
  use Property `(T)` in their load-bearing compression criterion.  In
  addition, nonsoficity alone is not a weak-MF obstruction.

No item above supplies the missing unconditional LCS witness or the
binary-Leavitt Atomic Morita Return compiler.  The strongest honest result
of this pass is therefore the closed property-`(T)`-free conditional theorem
`perfect-lcs-gap-implies-weak-non-mf`, together with the exact statement of
the construction still required.
