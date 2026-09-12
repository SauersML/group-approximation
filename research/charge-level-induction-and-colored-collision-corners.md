---
rg: 2
id: charge-level-induction-and-colored-collision-corners
kind: route
title: Fill each lower charge level before using a colored collision corner at the next level
target: finite-injective-charge-noncreation-forces-surjectivity
requires:
  - relative-equality-piecewise-injections-are-surjective
  - finite-injective-conservative-binary-automata-are-surjective
---

We prove the claim directly, allowing real weights. The bounded-cluster
Hall construction from the binary claim is extended below to colored
tokens. Its use at one charge level requires conservation only at that
level and below, which is supplied by induction.

## Replace charge equalities by positive integer token counts

Index the k nonzero symbols and regard w as a vector in R^k. Let L be
the rational span of all integer vectors d with w dot d=0. This is
a finite-dimensional rational subspace of Q^k. Its real annihilator
contains w, a strictly positive vector. Rational points are dense in
this rationally defined annihilator, so choose a strictly positive
rational vector there and scale it to a positive integer vector v.
Consequently, for nonnegative integer count vectors nu and eta,

    w dot nu = w dot eta  implies  v dot nu = v dot eta.       (CN1)

There is no requirement that v preserve charge inequalities. Nor is
an algorithm for finding all relations among the real weights asserted.

Use the candidate real charge levels

    Q={w dot nu : nu in N^k}.

Every actual configuration charge belongs to Q; when G is finite,
some levels in Q can have empty configuration sectors. The set Q
is locally finite: below any real bound each coordinate of nu has
a finite bound, since all w(a)>0. For q in Q, define N(q)=v dot nu
for any nu with w dot nu=q. This is well-defined by (CN1). Different
real levels may have the same N(q); we will keep them separate by
finite control-state conditions.

## Induct over the locally finite real charge levels

The level zero is the singleton zero configuration. Suppose all
levels below q are preserved and attained. If a configuration x of
charge q had image y of lower charge, the inductive surjectivity would
give a configuration z of that lower charge with tau(z)=y. This
contradicts finite-configuration injectivity, because W(x)!=W(z).
Nonincrease therefore forces W(tau(x))=q for every x of charge q.
We have proved conservation on every finite configuration of charge
at most q.

It remains to attain the whole level q. Put N=N(q). Replace a state
a at position g by v(a) distinguishable tokens

    (g,a,j),                     1<=j<=v(a).

Every charge-q configuration has exactly N such tokens. Let X_q be
the set of ordered N-token lists which encode a configuration of
original charge q. A valid list contains at each occupied site one
complete packet (a,1),...,(a,v(a)), for exactly one symbol a; no token
is repeated. These conditions use only finite control-state tests and
equalities of positions. Requiring charge q is also a finite
control-state condition: with N fixed there are only finitely many
possible symbol count vectors. Thus X_q is a definable subset of
C x G^N for a finite control set C, in the sense of the required
piecewise-injection theorem.

## Match the bounded clusters with colored tokens

Choose memory M containing 1_G and put E=M^(-1)M. The E-components
of the occupied input sites evolve independently, with disjoint
output supports, because no translated memory meets two components.
Every component has original charge at most q. Conservation through
q and (CN1) therefore preserve its integer token count as well.

Consider a component with output token set Y, and any subset Z of Y.
Let P be the output sites carrying tokens of Z. Truncate the input
component to its occupied sites in PM. Every local input at a site
of P is unchanged, so its entire output state is unchanged. The
truncated input has original charge at most q, and hence preserves
integer token count by the already proved conservation and (CN1).
Its output contains at least all the selected tokens. Therefore

    |Z| <= number of input tokens at sites in PM.             (CN2)

This is Hall's inequality for the finite graph joining an output
token at y to every input token at a site in yM. Input and output
token sets have equal cardinality, so a perfect matching exists.

The component's translation stabilizer H is finite and acts freely
on its tokens, since it acts freely on their sites. Injectivity and
equivariance give the same stabilizer for its output. Apply (CN2) to
unions of output H-orbits and divide by |H| to obtain Hall's condition
on the orbit graph. A perfect orbit matching lifts, by choosing an
adjacent representative pair and translating it by H, to an
H-equivariant token matching. Every matched input-output pair has
coordinate displacement in M^(-1).

There are at most N occupied sites in a component. After rooting at
one site, its support lies in E^(N-1); symbols come from a finite
alphabet. Hence only finitely many component types occur. Choose one
equivariant matching for each translation class of colored components
and translate it to every copy. Stabilizer equivariance makes the
result independent of the translation chosen from the representative,
so the matching depends on the configuration, not on its token ordering.
These choices depend only on the finite relative-equality and
control-state data specifying the rooted component.

## Apply the finite collision corner at this one level

Send each token in an ordered list in X_q to its matched output token.
The result belongs to X_q by conservation at q. Its piecewise form is
exactly a change of finite control state and a coordinate translation,
with a finite Boolean combination of relative equalities selecting
the branch. The map is injective: equality of output token lists
determines the same output configuration, finite injectivity determines
the same input configuration, and the fixed matching determines the
input ordering.

The required piecewise-injection theorem makes this map onto X_q.
Passing to unordered packets proves surjectivity on the charge-q
configuration sector. This completes the induction. Empty sectors
cause no difficulty; for q>0 with an actual configuration, N(q)>=1.

Every finite configuration is now attained and retains its charge.
Finite configurations are dense in A^G, while the continuous image of
the compact full shift is closed. Thus tau is surjective on A^G.
The argument never needs global injectivity or a local inverse.
