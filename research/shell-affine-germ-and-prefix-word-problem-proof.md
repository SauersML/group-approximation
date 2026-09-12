---
rg: 2
id: shell-affine-germ-and-prefix-word-problem-proof
kind: route
title: Decide every candidate singular germ and finish with a finite prefix calculation on the compact complement
target: arithmetic-shell-envelopes-have-decidable-word-problem
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

All arithmetic below is exact. A near arithmetic map is represented
by a tail threshold and finitely many formulas f(m*k+r)=a_r*k+b_r
with positive integer a_r. The map is a bijection between cofinite
sets; a finite exceptional domain or range is ignored only when
computing its germ.

## Effective germ calculus

These representations are effectively closed under composition.
To compose f with a map whose domain residues are taken modulo l,
refine each source progression by k modulo l/gcd(a_r,l). On each
refinement the intermediate residue is fixed and substitution gives
another affine formula. Increase the tail threshold to ensure all
intermediate arguments lie in their valid tails. Positivity makes
this a finite arithmetic calculation. Shifts n->n+c are included.
The inverse is obtained by inverting the affine maps on their image
progressions and refining to a common period. Cofinite bijectivity
ensures that these inverse image progressions partition a tail.

A represented near map is the identity exactly when every eventual
formula equals its input, that is, a_r=m and b_r=r in the displayed
coordinates. Thus germ identity is decidable and, in the positive
case, an explicit tail on which the map is identity is available.
All finite local-validity thresholds can be retained during the
same compositions, rather than just retaining an equality of germs.

## Candidate singular points and their germs

Write an input word as w=a_k*...*a_1, each letter a prefix generator
of V or one of the specified shell generators or inverses. Points
of Omega are stored as finite binary words followed by 0^infinity.
Their images and preimages under all these generators are computable:
use a finite prefix table, or locate the first 1 and evaluate rho
on the resulting integer shell index. The point p is fixed by all
shell letters.

Form the finite candidate set

    F={(a_(j-1)*...*a_1)^-1(p): a_j is a shell letter}.

Outside F, no intermediate trajectory encounters a singular point
of a letter, so w is locally V. If w moves any point of F, it is
nonidentity. Otherwise fix q in F and follow its trajectory z_j.
Choose effective V transporters t_z with t_z(p)=z and t_p=1.
Normalize each letter near p as

    t_(z_j)^-1*a_j*t_(z_(j-1)).

If a_j is a shell letter and z_(j-1)=p, this germ is exactly its
specified rho map. Otherwise the letter is locally a prefix map,
so the normalized germ is a shift n->n+c. The finite prefix or
shell table computes c and a cone on which that prefix description
holds. The normalized germs telescope to t_q^-1*w*t_q because
w(q)=q. The preceding arithmetic calculus decides whether this
germ is identity. A nonidentity germ proves w!=1.

If it is identity, the retained validity thresholds produce N_q
such that t_q^-1*w*t_q is the identity on every shell of index
at least N_q, and on p. Increase N_q until t_q is a single prefix
map there. Then U_q=t_q(0^(N_q)*C) is a computable clopen cone
around q on which w is identity. This is a neighborhood certificate,
not merely the assertion that the germ vanishes.

## The remaining compact calculation

After every candidate germ passes, remove the union of these U_q
and let D be its compact clopen complement. Compute the action
of w on D as a finite prefix table, one letter at a time.
Before any shell letter a_j, the current image of D avoids p:
its unique preimage under the preceding letters is a member of F,
which was removed. A compact clopen set avoiding p is contained
in finitely many shells, so that letter acts there by finitely many
explicit prefix replacements. Prefix letters are handled by finite
refinement in the usual way. Every step therefore remains a finite
prefix-table calculation.

The resulting table is identity exactly when each source prefix
equals its target prefix after refinement. Together with the
identity certificates on the U_q, this decides w=1 globally.
If F is empty, only the finite prefix calculation is needed.
All searches and arithmetic operations above terminate for the
specified finite data. Enumerating the words decided trivial
then gives a recursive presentation; it need not have finitely
many relators.

## Complexity of the input group

For fixed generator data, each rho_g(n) is bounded by C*(n+1)
for one constant C, and its branch is found by a fixed-modulus
calculation and finitely many exceptional comparisons. Iterating
a word of length l from 0 keeps integers of O(l) binary digits.
Fixed-integer multiplication, division, and residue computations
use O(l) elementary bit operations per step, giving O(l^2) such
operations overall. The word is identity in P exactly when its
even-index image of 0 is 0, because that action is free. This is
the asserted polynomial bound for P, not a runtime bound for the
whole shell-envelope algorithm.
