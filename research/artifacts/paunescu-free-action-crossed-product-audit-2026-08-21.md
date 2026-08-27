# Audit: free-group pmp actions and the singular relation quotient

Primary source: Liviu Păunescu, *On Sofic Actions and Equivalence Relations*,
arXiv:1002.0605.

The exact statements used are:

- Definition 1.3: an action is hyperlinear when its crossed product embeds in
  `R^omega`.
- Definition 1.4: a sofic action has such an embedding with diagonal base and
  permutation actor unitaries, hence is hyperlinear.
- Proposition 3.3: every action of `Z` admits a sofic embedding.
- Proposition 3.6: a countable free product of sofic actions over a common
  amenable subgroup is sofic.
- Corollary 3.7: every action of a free group, including `F_infinity`, is
  sofic.
- The discussion preceding Example 1.11 distinguishes the Feldman--Moore
  algebra from an ordinary crossed product; they agree for a free action.

The last restriction is load-bearing.  If an action has stabilizers, the
covariant formulas still define a representation of the **algebraic** crossed
product in the relation algebra, but group elements which agree on a
positive-measure set become the same orbit arrow there.  For the Manzoor
non-cohyperlinear IRS realization, this representation cannot be normal:
Păunescu's Corollary 3.7 makes the source von Neumann crossed product CE, while
the target relation algebra contains the non-CE IRS GNS algebra.  A normal
surjection of finite von Neumann algebras is a central-summand quotient and
would preserve CE.

This also explains why Păunescu's Proposition 3.8 embeds a treeable relation
algebra into a free-group crossed product using partial graphing isometries but
does not do so for arbitrary relations.  A treeing has no cycle word to create
stabilizer identifications.  In the non-CE IRS relation those identifications
are exactly the singular part that the faithful crossed-product trace refuses
to forget.
