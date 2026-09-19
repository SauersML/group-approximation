# Common-corner literal context audit (2026-08-21)

## Question

Can every finite context algebra be put behind one projection `q`, with each
binary marginal the compression of a literal group involution, and can those
literal marginals then be identified by ordinary amalgamation?

## Exact answer

The local part is always possible.  For each context use its selected finite
signed-permutation type, take the direct product of all context groups, tensor
their irreducible types, and multiply their primitive central idempotents.
The resulting single primitive projection `q` supports every context's exact
allowed-assignment diagonal algebra.  Every marginal is `q d_(c,x)` for a
literal involution in one direct-product factor.

The compatibility part cannot be accomplished inside any finite graph of
finite groups.  If `qgq` is a corner unitary, positivity forces `gq=qg`, so a
single compressed literal word has no partial-compression flexibility.  If
shared literal marginals nevertheless satisfy all BCS overlap and predicate
relations in `q C[Pi] q`, they define a unital BCS representation there.  But
the fundamental group `Pi` of a finite graph of finite groups is virtually
free.  Its normalized canonical corner trace is Connes embeddable, producing
a CE trace on the BCS algebra.  This contradicts the chosen BCS, which has no
CE trace.

## Boundary with previous Cairn results

This does not repeat the finite central-sign induction obstruction.  A
primitive type projection *does* prune arbitrary predicates, and tensoring
puts all local prunings behind one common `q`.  Nor is this merely the finite
root-block obstruction: the Bass--Serre corner `q C[Pi] q` is generally
infinite-dimensional.  The obstruction is canonical-trace permanence for the
whole virtually-free group.

Thus the remaining signed-Hecke problem is exactly cross-context holonomy
outside finite Bass--Serre geometry.  A literal one-piece compression cannot
provide block escape; the existing multi-piece corner transports are not an
optional convenience but the first syntax capable of leaving this no-go.
