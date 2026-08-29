import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.FreeGroupResiduallyFinite

/-!
# Question 3.4 reduces to finitely generated groups

Both soficity and hyperlinearity are defined by quantifying over finite subsets,
so neither can see beyond the subgroup a finite subset generates.  Made precise
that is a reduction of Pestov's Question 3.4 itself: *if every finitely
generated hyperlinear group is sofic, then every hyperlinear group is sofic*.

Two ingredients, both restrictions and nothing more.  Soficity passes along an
injective homomorphism -- that is `isSofic_of_injective` of `SoficTransfer` --
and it is *local*: a model of a subgroup extends to the ambient group by sending
everything outside the image to the identity.  The guard has to be membership in
the image rather than in the finite test set, since the multiplicativity
condition names `g * h`, which need not lie in the test set but does lie in the
image.

Given a finite `F ⊆ G`, the subgroup it generates is finitely generated, and
hyperlinear by `isHyperlinear_of_injective`; the hypothesis makes it sofic; and
locality carries a model back to `G`.  So nothing is lost by restricting
Question 3.4 to finitely generated groups, which is where its known candidates
live in any case.

This does not decide the question.  It says the general case follows from the
finitely generated one.
-/

/-! ## The two useful forms of the reduction

The reduction is worth stating twice more, because the forms one reaches for are
different from the form one proves.

As an *equivalence*: Question 3.4 holds in general exactly when it holds for
finitely generated groups.  One direction is the reduction; the other is
immediate, a finitely generated group being a group.

As a statement about *counterexamples*: a counterexample exists exactly when a
finitely generated one does.  This is the contrapositive, and it is the form a
search would use -- it says a hunt may restrict to finitely generated groups
without loss, which is not obvious from the definitions since neither property is
visibly inherited upward.
-/

/-! ## Universal hyperlinearity is also local

The same argument does not require a sofic conclusion.  If some group of any
cardinality is not hyperlinear, one of its finitely generated subgroups is
already not hyperlinear.  This is useful when a proposed source of a
counterexample is naturally uncountable, such as the abstract projective
unitary group of a finite factor: cardinality is not the obstruction.  The
substantive gate is proving that the ambient abstract group is nonhyperlinear
in the first place.
-/

/-! ## Arbitrary quotient permanence is the whole problem

Every group is a quotient of the free group on its underlying type, and free
groups are sofic, hence hyperlinear.  Therefore closure of hyperlinearity
under arbitrary quotients would imply universal hyperlinearity.  The converse
is tautological.  This explains why a non-Connes-embeddable finite-factor
representation of a hyperlinear group does not by itself produce a
nonhyperlinear group: promoting that representation to quotient permanence is
already equivalent to solving the universal problem positively.
-/

/-! ## The profile of a counterexample

Assembling what is already proved, a hyperlinear nonsofic group -- if one exists
-- is constrained on several sides at once, and the constraints are worth having
in one place.

It may be taken finitely generated, by the reduction above.  It is not locally
embeddable into finite groups, since `isSofic_of_isLEF` would make it sofic; a
fortiori it is not residually finite, by `isLEF_of_residuallyFinite`; and it is
infinite, a finite group being residually finite.  These are exactly the
constraints assembled below.
-/

/-! ## Monotonicity in the accuracy

Both local definitions quantify over all positive `ε`, and both model types get
weaker as `ε` grows -- multiplicativity is an upper bound on the defect and
separation a lower bound of the form `1 - ε` or `2 - ε`.  So a model at one
accuracy is a model at every worse accuracy, and it is enough to test the
definitions on any set of accuracies accumulating at `0`.

Cheap, but worth having: without it the definitions look as though they might
depend on which `ε` are tested, and several arguments below quietly need that
they do not.
-/

/-! ## The textbook convention for hyperlinearity

`isSofic_iff_productRestricted` records that requiring multiplicativity for all
pairs in the test set is the same as requiring it only when the product remains
in the set, because one may enlarge `F` by `F * F`.  The same comparison is
proved here for the hyperlinear definitions.

The argument is the sofic one verbatim: nothing about the metric enters, only
that enlarging the test set makes the hypothesis stronger and the products
available.
-/

/-! ## The separation constant: where the two sides part

The other convention is the separation constant.  On the sofic side it is
immaterial: `isSofic_iff_weak` shows that pinning separation at any fixed
`δ ∈ (0,1)` gives the same class, tensor powers driving a fixed separation to the
maximum while multiplying the defect only by the number of factors.

On the unitary side only one direction is established here.  The easy
direction is below.  `tensorPow_phase_collapse` shows why the permutation
amplification argument does not transfer: `1` and `i·1` are unitary,
maximally separated, and have equal fourth tensor powers.  Accordingly the
formal API records only the direction proved in this corpus.
-/

/-! ## The reduction discharges the countability hypothesis

`exists_hyperlinearApproximation_of_isHyperlinear` carries a `[Countable G]`
hypothesis, needed to exhaust the group by finite test sets.  The reduction makes
that hypothesis free of charge: a finitely generated group is countable, being a
surjective image of a free group on finitely many generators, so a counterexample
may be taken countable.
-/
