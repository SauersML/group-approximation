# Weighted prefix recodings remain elementary amenable despite component splitting

Date: 2026-09-08. A finite-prefix involution commuting with both Q
and the balanced triangular rule can split one non-u component
into two. Thus the old non-u-count invariant does not constrain
all finite-prefix centralizers. Nevertheless all finite-prefix
Q-centralizing recodings, even combined with the existing finite
diagonal tail actions, lie in a larger elementary amenable group.
They cannot supply a Gottschalk counterexample.

The stronger invariant is the total number of non-111 right-t
triples. Finite Q^2-fiber cardinalities force its preservation.
A faithful finite-weight stratum then places each finitely
generated subgroup inside the known elementary amenable group
of piecewise lattice isometries on finitely many orthants.

The theorem concerns the finite prefix diagrams defined below.
It does not classify arbitrary Q,F_A centralizers or arbitrary
infinite component permutations. No headline conjecture is solved.

## Component weights forced by quadratic fibers

Keep the component system from
[the invariant-code construction](gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md):

    D=(F_2^{A_4})^2,    X=D^N,    u=(1,1),
    t=(123),    h=(12)(34),    A=I+R_h,
    F_A(x,y)=(x+A Q_t(y),y).

The operation Q applies Q_t(x)=x R_t x separately to both tracks
of every component. There are four right-t triples on each track,
hence eight per component. On a triple, Q_t^2 sends 111 to 111
and every other state to 000. Set

    w(d)=the number of those eight triples of d that are not 111.

Then 0<=w(d)<=8, and w(d)=0 exactly when d=u. For z in X write
W(z)=sum_i w(z_i), allowing infinity. The fiber above Q^2 z has
cardinality

    |(Q^2)^-1(Q^2 z)|=7^W(z)       if W(z) is finite,

and is infinite otherwise. Each 000 triple contributes seven
independent choices, and each 111 triple contributes one.

Every homeomorphism H commuting with Q^2 gives a bijection between
this fiber and the fiber above Q^2 H(z). Consequently it preserves
every finite total-weight stratum exactly. This conclusion holds
for arbitrary such H, without a prefix hypothesis. It does not
alone imply amenability: arbitrary component permutations also
preserve all these weights.

The diagonal left A_4 action permutes the right-t triples, so it
preserves w and fixes u. The weight-eight class carries a faithful
A_4 action: its elements include every pair (delta_g,0), and these
detect the regular action. Weight-one labels also exist, for example
(x,1) with x equal to 1 except for one all-zero right-t triple.

## An exact splitting involution commuting with Q and F_A

Choose two distinct right-t triples J_0,J_1 in A_4. Define S on X
as follows. On the clopen predicate

    y_0=y_1=1,

swap the oriented x-triple J_1 between components 0 and 1, leaving
everything else fixed. Outside that predicate, act identically.
This is a finite-prefix involution. The orientation is the same
right-t order in both copied triples.

The predicate has its full Q-preimage equal to itself, since
Q_t^-1(1)={1}. Swapping complete oriented triples commutes with Q,
so S Q=Q S. The predicate is also F_A-invariant because F_A fixes
the y track. On the predicate, F_A fixes both affected components:
A Q_t(1)=A1=0. Outside it S is the identity. Thus S F_A=F_A S.

For a concrete split, take component 0 to have y_0=1 and x_0=1
except that J_0 and J_1 are both 000; take component 1 and all
later components equal to u. After S, component 0 has only the
J_0 defect and component 1 has only the J_1 defect. One non-u
component has become two. Both configurations are Q-fixed and
have Q^2-fiber cardinality 7^2=49, and Q-fiber cardinality 4^2=16.

The old prefix/permutation/globally controlled-diagonal group
preserves the number of non-u components, so S lies outside it.
Its existence does not establish nonamenability of an enlargement.

## The larger weighted prefix group

Let P_w be the group of homeomorphisms described by finite prefix
diagrams

    p eta -> q gamma eta,             gamma in A_4,          (1)

where p and q are finite words in D, the source prefixes form a
complete disjoint prefix code, the target prefixes do likewise,
and gamma acts diagonally on every letter of the suffix eta.
Require each branch to satisfy

    w(p)=w(q),                       w(p)=sum_{d in p} w(d). (2)

Inverse and composition stay in this class by finite prefix-code
refinement. Tail actions form a finite group and preserve weights;
inverting a branch or refining it by further letters preserves
(2). Equivalently these are finite, weight-preserving prefix
replacements with an A_4 action on the remaining suffix.

Any diagram of the form (1) which commutes with Q^2 automatically
satisfies (2): apply finite-weight preservation to p u^infinity,
whose image is q u^infinity. Thus all pure finite-prefix Q,F_A
centralizers are in P_w. The prior Gamma_data also lies in P_w:
its prefix maps and finite component permutations preserve weight,
and a finite-data-selected global action has branches
p eta -> gamma(p)p gamma(p)eta. The splitting involution S is a
weight-preserving permutation of the first two component values,
so it is in P_w as well.

Not every element of P_w is claimed to commute with Q or F_A.
It is a containing group, large enough to close the proposed
finite-prefix enlargement route.

## Faithfulness on one finite-weight stratum

Fix finitely many elements of P_w and their inverses, with diagrams
of the form (1). Let b be the maximum weight of any source or target
prefix in these diagrams. Define

    n=b+16,       X_n={z in X : W(z)=n}.

The generated subgroup preserves X_n. We prove its restriction
there is faithful, despite possible splitting and merging of
non-u components.

For any input of total weight greater than b, mark the first letter
at which cumulative weight exceeds b. Call this the boundary
letter, and let m be the weight of the prefix ending there. Then

    b+1 <= m <= b+8.

No branch prefix of a generator can contain the boundary letter:
such a prefix would have weight greater than b. Every generator
therefore replaces only a prefix strictly before it and applies
one common diagonal action to the boundary letter and the entire
remaining suffix. Because both prefix and tail actions preserve
weight, the boundary remains intrinsically the first letter
crossing b. This remains true throughout every word in the chosen
generators. All decisions made by that word are independent of
the data at and beyond the boundary; the common tail multiplier
may depend on the earlier data.

Suppose a word acts identically on X_n. Fix an arbitrary input z
of total weight greater than b and retain its prefix through the
boundary letter. Append b+8-m copies of one weight-one label,
then one variable weight-eight label v, then u^infinity. Each
resulting test input has total weight

    m+(b+8-m)+8=n.

The word makes the same decisions on all these test inputs and
on z. On their suffixes starting at the boundary it applies one
common multiplier gamma, independent of v. The appended v is
the last non-u component; no prefix replacement can reach it,
and a diagonal action fixes u and preserves positive weight.
Identity on X_n therefore gives gamma v=v for every weight-eight
label v. Faithfulness on that class forces gamma=1.

Identity of the test input also fixes its intrinsic boundary
position and the entire preceding prefix. Those are the same
prefix decisions as on z. Its suffix receives gamma=1, so the
word fixes z. Inputs of total weight greater than b are dense
in X; continuity now makes the word the identity everywhere.
This proves faithful restriction to X_n. The choice of n depends
on the finite generating set, not on word length.

## The finite-weight stratum is a finite union of orthants

Every element of X_n has a finite positive-label word

    (d_1,...,d_j),    d_i!=u,    sum_i w(d_i)=n.

There are finitely many such words and j<=n. For a fixed word,
the U gaps preceding its labels identify the corresponding part
of X_n with N^j. Thus X_n is a finite disjoint union of orthants
of possibly different ranks.

Fix a prefix branch and a positive-label word. If the branch
prefix contains k positive letters, its first k gaps are fixed.
When positive letters remain in the suffix, the next gap is lower
bounded and later gaps are free. Replacing p by q fixes the new
prefix gaps and translates that first suffix gap by the difference
of trailing U lengths. All later gaps are copied. The suffix
multiplier only changes the finite label-word copy.

The number of free coordinates is the number of positive suffix
letters, and is the same on both sides, even when the total
numbers of positive letters differ. If no positive suffix remains,
the source and target pieces are points. Refining over the finitely
many branches and label words therefore makes every restricted
generator a finite piecewise lattice isometry of this orthohedral
set. One can realize its orthant copies disjointly in Z^(n+1),
using the last coordinate to label the copies.

Bieri and Sach prove that the piecewise Euclidean isometry group
of any orthohedral set is elementary amenable:
[Theorem 4.4(i)](https://arxiv.org/html/2110.05788),
[Journal of the London Mathematical Society (2022)](https://doi.org/10.1112/jlms.12503).
The faithful restriction therefore proves each finitely generated
subgroup of P_w elementary amenable. Directed unions give the
same conclusion for all of P_w. This applies a known orthant
theorem; no novelty of that theorem is asserted.

## Consequence and remaining scope

The subgroup generated by the old source symmetries and any
finite-prefix Q,F_A-centralizing recodings is elementary amenable,
even when recodings split or merge non-u components. Consequently
every finite-alphabet full-shift cellular automaton over that
group is surjunctive, by the amenable Garden-of-Eden theorem of
Ceccherini-Silberstein, Machi, and Scarabotti,
[Amenable groups and cellular automata](https://www.numdam.org/articles/10.5802/aif.1686/).
For a non-finitely-generated ambient group, restrict the local
rule to the subgroup generated by its finite memory and then
apply the result independently on left cosets.

The splitting gate disproves conservation of non-u component
count. It respects the finer total triple weight, and its entire
finite-prefix enlargement remains inside a surjunctive group.
An arbitrary infinite permutation of component positions need
not have a finite prefix diagram and is outside this closure
theorem. Since such permutations already realize arbitrary
countable group actions, merely adjoining one does not furnish
a new Gottschalk mechanism. In particular the full Q,F_A
centralizer cannot be elementary amenable: a regular permutation
action on the countable component set embeds the free group on
two generators into it. That abstract embedding supplies no
injective nonsurjective cellular automaton. The universal
Gottschalk conjecture remains unresolved.
