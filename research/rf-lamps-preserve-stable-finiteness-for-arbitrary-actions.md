---
rg: 2
id: rf-lamps-preserve-stable-finiteness-for-arbitrary-actions
kind: claim
title: Residually finite lamps preserve stable finiteness over any permutation action and any stably finite base group algebra
distinct_from:
  rf-lamps-with-finite-stabilizers-preserve-direct-finiteness: that transfers direct finiteness at each fixed size using finite-rank perturbations; this removes the finite-stabilizer hypothesis for stable finiteness by a different induction.
  rf-lamp-permutational-wreaths-satisfy-stable-finiteness: that assumes residual finiteness of both lamp and base groups; this only assumes it for the lamp and assumes stable finiteness of the base group algebra itself.
  wreath-finiteness-transfers-from-product-closed-classes: that uses finiteness of a subgroup-and-product-closed class containing both groups; this avoids powers of the base group by retaining one diagonal group action.
---

Let k be any field, A a residually finite group, G any group, and X any
G-set. Put W=A wr_X G=(direct_sum_X A) semidirect G, with the restricted
permutation action and no internal automorphism twists. Then

    k[W] is stably finite if and only if k[G] is stably finite.

No residual finiteness of G, finite-generation assumption, stabilizer
restriction, or relation between lamp torsion and char(k) is required.
The theorem concerns stable finiteness; it does not extend the earlier
fixed-matrix-size equivalence to arbitrary infinite stabilizers.

The proof retains one diagonal group action in the marked-site tensor
construction. If C is the external unitization of direct_sum_X k[A],
the relevant algebras are

    R_r(H,j)=(k[A^j] tensor C^(tensor r)) semidirect H,
                    H<=G, r,j>=0.

Deleting one C factor gives a split quotient R_(r-1)(H,j). Its ideal
is a direct sum of finite-support matrix algebras over
R_(r-1)(H_o,j+1), for orbit stabilizers H_o. Thus induction only takes
subgroups of G and adds RF lamp factors; it never requires stable
finiteness of new direct powers of G. Finite-dimensional regular
representations of finite lamp quotients supply the base cases.

More generally, the proof only needs k[A^j x H] to be stably finite
for every finite j and H<=G. Residual finiteness of A together with
stable finiteness of k[G] verifies exactly that hypothesis.

As a consequence, for every finite nonempty alphabet B and every G-set X,

    C_lc(B^X,k) semidirect G is stably finite
        if and only if k[G] is stably finite.             (DWI1)

Here G acts on B^X by permuting its X-coordinates. In particular,
replicating certificate values along arbitrary cosets G/H does not
create stable-finiteness failure over a base algebra that is stably
finite. This corollary concerns a full product of independently chosen
certificate symbols indexed by X; it does not concern arbitrary
constrained subshifts.

The lamp hypothesis extends to LEF in
`lef-group-rings-over-stably-finite-rings-are-stably-finite`, using exact
finite multiplication tables for the base coefficients. A separate
strengthening, `residual-lamp-quotients-handle-monomial-actions`, permits
internal automorphism twists when finite lamp quotients invariant under
all twists separate A; this includes every finitely generated RF lamp.
Neither result covers arbitrary twisted LEF lamps, unrestricted wreath
products, or nonsplit extensions, and neither resolves a headline
conjecture.
