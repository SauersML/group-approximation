# Effective generic shell actions and a presentation obstruction, 2026-09-08

The universal Boone--Higman presentation requirement remains open.
The new result rules out generic free-product near actions as a way
to satisfy it, including computable examples with decidable word
problem. It gives a necessary condition on the whole shell envelope;
the argument does not pass through finite presentation of A_1.

## Construct the free near action

For any countably infinite P, a dense comeagre set of enumerations
nu makes R_nu=<lambda(P),s> the free product P*<s>. Each nonidentity
reduced word can be assigned a fresh finite moved trajectory beyond
any specified index. Its P syllables use new pairs h,g*h, and its
shift blocks use fresh integer endpoints. Infinitude leaves room
after any finite prescription. Satisfy all these requirements and
interleave assignments making the partial bijection total both ways.

For a finitely generated decidable P this is an effective construction:
its word-problem algorithm handles normal forms and finite exclusions.
The resulting enumeration and its inverse are computable. This is
an existence algorithm with no claimed practical runtime or arithmetic
residue formula.

## Finite certificates, then a contradiction to finite presentation

At such a free near action, the parity-preserving shell germ group
is (P*Z) x_Z (P*Z). Identity reduces to two empty free-product normal
forms. Their cancellations use only identities already true for every
regular P action and the cofinite shift, so their tail validity depends
on finitely many enumeration and inverse values.

For a true whole-envelope relation, normalize the finitely many
candidate singularities, retain those tail certificates, and compute
the finite prefix table on their compact complement. Collecting the
finite queries proves the relation for every enumeration extending
that finite data. When P and nu are computable this also decides the
whole envelope word problem.

If finitely many such relations presented E_nu, their finite data would
permit a nontrivial swap of two unused enumeration values, preserving
nu(1). The same presentation would map onto the newly marked envelope
and fix V pointwise. Every nontrivial normal kernel contains V, so
this map would be injective. Conjugation of the localized prefix flips
would then recover identical regular permutations and hence identical
enumerations. That contradicts the swap.

Therefore E_nu is not finitely presented whenever its canonical near
shift group is P*Z. In particular any successful finite-presentation
enumeration MUST impose at least one additional mixed near relation.
This condition is not asserted sufficient.

## Effect on the universal route

Every infinite finitely generated decidable input has computable
enumerations giving decidable non-finitely-presented shell envelopes.
For perfect inputs these very same groups are simple and faithful.
Thus an effective action, simplicity, and a word-problem algorithm
still do not settle the required finite-presentation step.

For virtually cyclic inputs, both computable positive and computable
negative examples occur after every finite prescription. This supplies
computable failures of finite presentation of E itself; the earlier
dense negative examples relied on noncomputability. The universal
existential claim is not refuted because other enumerations can impose
additional near relations. The older ascending-HNN obstruction was a
necessary condition for A_1 to be finitely presented; the new argument
restricts finite presentation of E directly.

## The arithmetic benchmark avoids this obstruction

If lambda(m*k+r)=a_r*k+b_r with positive a_r, then
lambda*s^m*lambda^-1 translates each image progression by a_r.
It therefore commutes near infinity with s^A, where A is the least
common multiple of all a_r. This is an additional mixed near relation
which is nontrivial in the abstract free product when lambda comes
from a nonidentity input element.

For the bijective-base A5*A5 action the source modulus is 118, the
coefficients are 6962, 118, and 2, and A=6962. Thus every nonidentity
factor element a satisfies [lambda_a*s^118*lambda_a^-1,s^6962]=1.
The earlier arithmetic candidate passes this necessary test. Its
finite-presentation question stays open; the displayed relation
does not purport to present the near group or the Cantor envelope.

These are written proofs, with finite-certificate algorithms described
mathematically. Cairn structural checks do not replace verification of
the arguments. No new local code, build, GPU job, or Civo resource was
used to derive them.
