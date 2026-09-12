# The KL gate transported into the C3 corner chart

The KL coefficient

```text
q=x_34(s_1)x_(11,12)(t_0) in EL_20(R)
```

cannot be substituted into the corner equation merely from the abstract
isomorphism `EL_20(R) ~= R^x`; the prefix-code transport must be fixed.  The
repository supplies a canonical choice: the 20-leaf left comb

```text
alpha_i=1^(i-1)0  (1<=i<20),       alpha_20=1^19.
```

Under `Theta_alpha(M)=sum s_(alpha_i) M_ij t_(alpha_j)`, put

```text
A_q=s_(alpha_3) s_1 t_(alpha_4),
B_q=s_(alpha_11) t_0 t_(alpha_12).
```

The transported KL gate is

```text
qhat=(1+A_q)(1+B_q)=1+A_q+B_q.                         (1)
```

The two matrix roots are far apart, so `A_q^2=B_q^2=A_qB_q=B_qA_q=0`.
Consequently

```text
qhat^2=1.                                               (2)
```

This mixedness is intrinsic rather than an artifact of the 20-leaf display.
Apply the inverse two-leaf chart `Phi_2(z)=(t_i z s_j)_(i,j)`.  Its `(1,1)`
entry contains

```text
t_1 A_q s_1=s_101 t_0t_1t_1
```

and the distinct, longer reduced mixed monomial `t_1 B_q s_1`.  Prefix
normal form prevents cancellation between these terms or with the scalar
entry.  Thus this entry belongs to neither the `t`-coefficient nor the
`s`-coefficient free subalgebra, proving that `qhat` is outside both pure
coefficient charts.

For the inverse-pair packet ansatz, (2) makes both packets equal.  Its exact
corner identity is

```text
e(t~+[qhat]k[qhat])e(s~+[qhat]k[qhat])e=e,              (3)
```

or, with `P=e[qhat]k[qhat]e`,

```text
A P + P B + P^2=Delta.                                  (4)
```

The coordinate cycle transports to the prefix permutation

```text
phat=sum_i s_(alpha_(i+1)) t_(alpha_i)
```

(indices cyclically), so the twenty coordinate variants are
`qhat_j=phat^j qhat phat^-j`, again involutions.  Likewise a coefficient-one
root transports to

```text
1+s_(alpha_i)t_(alpha_j),
```

giving the short Steinberg-commutator candidates requested by the KL lane.

## What an exact test must certify

Expanding (4) gives a finite multiset of units of `R`.  Equality holds if and
only if every unit occurs with even multiplicity after including the two
terms of `e`.  Thus a positive certificate is an explicit pairing of all
terms by Leavitt-unit equality; a negative certificate is one term whose
prefix normal form differs from every other term.

The existing infinite-word verifier cannot test (4) by applying the *sum* to
basis vectors.  Evaluation of (4) in `R` is identically zero for every
conjugator, because `k` evaluates to zero and `t_0s_0=1`.  Such a test would
therefore return zero even when the formal group-algebra element is nonzero.
One must canonicalize or separately distinguish the individual unit terms.

The accompanying exact verifier does this in Bergman normal form, orienting

```text
s_1 t_1 -> 1+s_0t_0.
```

It checks the Cuntz relations and the order-twenty prefix cycle internally,
then audits every group-basis fiber.  The result is negative for all twenty
coordinate conjugates of `qhat`: their nonzero residues contain respectively
`122`, `164`, `224`, or `234` odd unit fibers.  It is also negative for all
`20*19=380` transported coefficient-one roots `x_ij(1)`; those residues have
`122`, `168`, or `176` odd fibers.  Thus none of the KL gate, its coordinate
orbit, or the simplest Steinberg-commutator/root candidates solves (3).  The
identity unit itself is an odd fiber in every one of these 400 residues, so
the negative certificate does not depend merely on a residue count.

The surviving mixed relation is the even-fiber condition

```text
supp-multiset(A P) + supp-multiset(P B)
  + supp-multiset(P^2) + supp-multiset(Delta) = 0 mod 2. (5)
```

Equation (5), with the closed formulas (1)--(4), is a bounded unit-equality
audit, not an unbounded search over the group.  The audit now shows that the
next candidate must involve at least two interacting mixed gates, or another
mixed word outside the tested KL coordinate orbit and single-root family.

## Two interacting KL gates

The next minimal family is also decidable without an enlarged search.  Put

```text
q_i=phat^i qhat phat^-i,       x_(i,j)=q_i q_j,
x_(i,j)^-1=q_j q_i.
```

The anchored family `x_(0,d)` has nineteen nontrivial relative distances.
Cyclic conjugation need not fix the corner lifts `A,B`, so the verifier also
audits all `20*19=380` ordered pairs rather than assuming that reduction.
Write `epsilon_1` for the coefficient of the identity unit in the group ring.
The exact normal-form audit proves, for every ordered pair,

```text
epsilon_1(Delta)=1,
epsilon_1(A P_(x^-1))=0,
epsilon_1(P_x B)=0,
epsilon_1(P_x P_(x^-1))=0.                            (6)
```

Therefore

```text
epsilon_1(A P_(x^-1)+P_x B+P_xP_(x^-1)+Delta)=1,      (7)
```

so no ordered product of two coordinate KL gates solves the inverse-pair
equation.  Across all 380 pairs the full residue sizes are `122`, `164`,
`202`, `224`, `234`, `236`, `238`, or `242`.  Equation (6), rather than those
counts, is the uniform obstruction for the whole family.  The next candidate
must mix distinct gate types, not merely two coordinate copies of the KL
gate.

## One KL gate and one pure-chart KL root

The other two coefficients in the original KL generator triple give the
involutions

```text
a=x_12(s_0),        f=x_12(t_1),
a_j=phat^j a phat^-j,       f_j=phat^j f phat^-j.
```

The verifier tests all 400 index pairs in each of the four ordered families

```text
q_i a_j,       q_i f_j,       a_j q_i,       f_j q_i,
```

with the reverse word used as the exact inverse.  This again avoids assuming
that the fixed corner lifts share the coordinate-cycle symmetry.  For every
one of the 1,600 words the same coefficient formula holds:

```text
epsilon_1(Delta)=1,
(epsilon_1(A P_(x^-1)), epsilon_1(P_x B),
 epsilon_1(P_x P_(x^-1)))=(0,0,0).                    (8)
```

Thus every distinct-type word in these four minimal families leaves the
identity fiber odd.  The full residue sizes range over
`122,156,164,202,220,222,224,234,236,238,242`; formula (8) is the uniform
certificate.  A surviving short conjugator must therefore use a longer
Steinberg interaction than one KL gate times one cyclic `s_0`- or `t_1`-root.

## Coordinate monomials and shortest Steinberg commutators

The last natural one-gate families use the order-twenty coordinate cycle
itself.  For every `i` and every `1<=j<20`, the verifier audits

```text
x=q_i phat^j,        x=phat^j q_i,
```

with their explicit reverse-order inverses.  All 760 words satisfy the same
identity-coefficient formula (8): the three correction bits vanish and the
base bit is one.

It also audits the two shortest commutator grids

```text
[q_i,a_j]=q_i a_j q_i a_j,
[q_i,f_j]=q_i f_j q_i f_j.
```

In each 400-word grid exactly 80 commutators are nontrivial in Bergman normal
form.  Every one of those 160 nontrivial commutators again has correction-bit
triple `(0,0,0)` and hence odd identity fiber.  The trivial commutators reduce
to the already-failed base word and have the same bit.

This exhausts the canonical short program consisting of one coordinate KL
gate, one coordinate-cycle monomial or one cyclic pure root, products in both
orders, and their shortest commutators.  It does **not** assert a theorem for
arbitrary prefix permutations or arbitrary longer Steinberg words.  Any next
constructive packet candidate must introduce either a second gate type not in
the KL triple, a noncyclic prefix permutation, or a longer nested commutator.
