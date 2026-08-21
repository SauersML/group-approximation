# André--Guirardel sharp-two property-(T) actor audit

Checked 2026-08-21 against the primary arXiv/published text of Simon André
and Vincent Guirardel, *Finitely generated simple sharply 2-transitive
groups*, Compositio Mathematica 160 (2024), 1941--1957,
arXiv:2212.06020.

Theorem 1.1 states that there is an infinite sharply two-transitive group
which is two-generated, simple, and has Kazhdan property `(T)`.  Theorem 1.4
adds exactly four conjugacy classes.  Sharp two-transitivity means the action
on ordered pairs of distinct points is transitive (indeed free), so the
diagonal action on `X^2` has exactly two orbits.

The source does not claim that the final group is finitely presented.  It
also does not state that a point stabilizer in the sharply two-transitive
action is finitely generated.  Those are precisely the two extra hypotheses
needed by the standard finite-presentation theorem for the binary
permutational wreath product, and therefore for its index-two augmentation
subgroup.

### Recursive-presentation audit

Direct finite presentation is not necessary for the nonhyperlinearity route:
a finitely generated recursively presented nonhyperlinear marked lamp group
can be Higman-embedded in a finitely presented overgroup.  The lamp extension
itself has an explicit recursive presentation if the actor does.  In the
action on involutions the point stabilizer is a centralizer, and equality
proofs in a recursive presentation recursively enumerate its word preimage.

The paper does **not**, however, state recursive presentability of its final
two-generated actor.  Section 4 chooses HNN steps according to semantic type
and maximality conditions.  Theorem 5.3 then forms a direct limit of
epimorphisms supplied by Proposition 5.6, which invokes an existential
small-cancellation quotient theorem.  No algorithm enumerating the kernels of
these chosen quotients is supplied.  Consequently recursive presentability
cannot currently be inferred from the published proof without an effective
refinement.  This is a strictly weaker gate than finite presentation; it is
not evidence that the actor is non-recursive.

Primary source: https://arxiv.org/abs/2212.06020
