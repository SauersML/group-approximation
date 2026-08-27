---
rg: 2
id: adaptive-prefix-atom-rank-return-does-not-close-opnorm-row
kind: claim
title: Adaptive prefix-atom rank rigidity does not produce an operator-norm return row
distinct_from:
  opnorm-packet-rank-does-not-yield-action-shadow: that audits fixed packet exactification and the normalizer/opposite-root boundary; this treats the proposed escape from that fence by growing a prefix orbit adaptively with the matrix dimension and appealing to rank recurrence.
  binary-leavitt-finite-actor-minimal-atom-dichotomy: that gives an exact crossed-product countermodel after one finite invariant actor packet has already been fixed; this treats the complementary proposal of growing the packet with the matrix coordinate and then invoking finite rank or absence of finite actor actions.
  exact-lamp-lifts-admit-moving-pair-kernel-jumps: that twists exact augmentation-lamp lifts at a moving pair; this gives the elementary projection-orbit obstruction before any particular lamp presentation or choice of exact lift.
  opnorm-leavitt-coarse-fine-return-row: that asks for the actual common-carrier return row from the full Steinberg presentation; this only rules out obtaining it from adaptive atom growth, projection distance below one, and actor simplicity by themselves.
---

**ESTABLISHED SCOPE FENCE.**  A dimension-dependent growing orbit of exact
spectral atoms need not contain any dimension-independent returned atom, even
when every displayed transport is exact and every atom has the least possible
nonzero rank.

Indeed, for every `L>=1` take `H_L=C^(L+1)`, let

```text
P_(L,j)=projection onto C delta_j,                 0<=j<=L,
W_(L,j) delta_(j-1)=delta_j,                       1<=j<=L,
```

and extend each displayed one-row transport to a unitary arbitrarily on the
orthogonal complement.  Then

```text
W_(L,j) P_(L,j-1) W_(L,j)^*=P_(L,j)                (APR1)
```

with zero error, all the projections have rank one, and the first `L+1`
atoms are pairwise orthogonal.  Thus neither least-rank selection nor the
fact that projections at operator distance less than one have equal rank
forces a return in a word window independent of `L`.  The latter fact is only
a rank statement: for two distinct rank-one projections making angle
`0<theta<pi/2`,

```text
||P-Q||_op=sin(theta)<1                              (APR2)
```

although `P!=Q`.

The same point identifies exactly why simplicity or absence of finite actor
actions cannot be invoked at this stage.  Those hypotheses apply only to a
homomorphism

```text
Actor -> Sym(O)                                      (APR3)
```

on one **finite invariant** atom set `O`.  A growing prefix window is a
partial action: a boundary atom is sent to a new atom outside the current
window.  Enlarging the window merely replaces `(APR1)` by a longer exact
path.  Finiteness of each matrix coordinate permits the first return length
to grow with its dimension, and supplies no fixed word or fixed modulus.

Turning the partial action into `(APR3)` requires all of the following before
actor simplicity becomes relevant:

1. one exact joint PVM for the whole moving root/lamp window;
2. actor covariance on every atom selected after seeing the coordinate, with
   an operator-norm error strictly below the orthogonality threshold; and
3. closure of that PVM under every actor generator.

Pointwise corona covariance gives these statements for each fixed atom, not
uniformly over the moving frontier.  This is not repaired by choosing exact
commuting torsion lifts: `exact-lamp-lifts-admit-moving-pair-kernel-jumps`
exhibits exact lifts whose fixed corona classes agree while their moving
kernel jumps have operator norm two.  If instead one freezes a finite
invariant normalizer packet from the outset, then
`binary-leavitt-finite-actor-minimal-atom-dichotomy` supplies exact
Morita-neutral crossed-product models.  Hence the adaptive and frozen
versions cover the two sides of the same gap.

The native marked root-star does not alter this conclusion.  Its three
anchored cells give a powerful **fixed finite** common carrier, but they do
not make the whole prefix orbit normalize one finite character PVM.  Iterating
the locally wordized binary split also does not manufacture such a PVM:
`binary-leavitt-root-doubling-k0-retains-xor-overlap` gives an exact stationary
four-atom model in which the parent and both child negative projections have
equal rank while the child cuts retain a nonzero intersection.  Thus local
parent/child conjugacy plus rank rigidity remembers XOR, not the additive
orthogonal-union identity needed by the coarse/fine return row.

Consequently the ingredients

```text
adaptive prefix growth
+ rank(P)=rank(Q) whenever ||P-Q||<1
+ no nontrivial finite action of the prefix actor                  (APR4)
```

do **not** imply the common-carrier estimate `(OPLR)` of
`opnorm-leavitt-coarse-fine-return-row`.  A successful proof must add a
coefficient-sensitive uniform closure theorem which produces `(APR3)` (or
produce the return row directly).  This fence does not refute such a theorem
from the full Steinberg presentation, and therefore does not refute the
Property-`(T)`-free non-MF goal.

DERIVATION
adaptive-prefix-atom-rank-return-fence-proof
