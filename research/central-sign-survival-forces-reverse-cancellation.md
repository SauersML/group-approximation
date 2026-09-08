---
rg: 2
id: central-sign-survival-forces-reverse-cancellation
kind: claim
title: Survival of the central sign in a matching presentation forces the reverse inverse
distinct_from:
  cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect: that uses commuting roots of unity and integral lattice relations; this permits noncommuting coefficients and detects an actual central double cover of the matching group.
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that excludes bounded support pairs by enumerating universal groups; this excludes any template whose signed central extension retains its sign, at arbitrary support sizes.
artifacts:
  - research/artifacts/cancellation-phase-lift-literature-audit-2026-09-07.md
  - research/artifacts/c4-cancellation-needs-eighth-root-phases-2026-09-07.md
  - research/artifacts/seven-face-central-sign-collapse-2026-09-07.md
  - research/artifacts/coupled-seven-face-completions-2026-09-07.md
---

Suppose B=sum_i[t_i] and A=sum_j[s_j] in F_2[G] satisfy BA=1.
Choose a pivot cell with product 1 and pair all remaining cells with
equal-product cells. Reindex so the chosen pivot is (0,0). Form the
signed matching group H with generators X_i,Y_j,J and relations

    J^2=1,       J central,       X_0=Y_0=1,
    X_i Y_j = J X_k Y_l for each paired cell ((i,j),(k,l)).

If J is nonidentity in H, then AB=1 in F_2[G]. In particular, any
strict inverse pair forces J=1 in EVERY such signed matching group,
for every permitted pairing and pivot.

No finite-dimensional representation, finite quotient, soficity, or
amenability of H or G is required. The proof uses the integral twisted
coefficient ring Z[H]/(J+1). When J survives, that ring embeds in a
characteristic-zero group-algebra corner; a forward inverse identity
there reverses, and coefficient augmentation modulo two recovers AB=1.

This contains the scalar phase criterion: compatible scalar phases
normalized at the chosen pivot give a representation of H with J=-1.
It is strictly stronger on actual inverse rectangles. The attached C_4
example has a matching for which no scalar phases exist, but its signed
relations have a D_8 realization with J the nonidentity central
involution. Thus noncommuting coefficient lifts exclude that matching.

There is also an exact diagram criterion. In the free group F on the
normalized X_i,Y_j, let

    r_e=X_i Y_j (X_k Y_l)^(-1).

Then J=1 in H if and only if there is an identity in F

    product_(a=1,...,q) w_a r_(e_a)^(epsilon_a) w_a^(-1)=1,
    epsilon_a in {1,-1},          q odd.                (CSI1)

Consequently a strict inverse template requires such an odd closed
relator identity, not merely an odd integral relation after abelianizing
the support generators. In particular, an aspherical ordinary normalized
matching presentation is excluded. The relevant asphericity is that of
this displayed presentation complex, not just existence of some other
aspherical presentation of the same group.

Neither collapse of J nor (CSI1) suffices to show AB!=1. These tests
identify required algebraic feedback in a proposed closed verification
circuit; a surviving counterexample still needs a literal reverse
defect. No such counterexample is constructed here.

The seven-face artifact supplies an explicit boundary example: seven
disjoint pairs in a complete 7-by-7 inverse rectangle force J=1. Yet
the ordinary universal group of that completed matching is exactly
C_2^3, and its two universal factors coincide and square to one. This
proves directly that passing the central-sign-collapse requirement is
insufficient, even with all support labels still distinct. The rejected
candidate is completely classified, not merely checked in a finite
quotient or bounded word ball.

A different completion of the same seven seed pairs has unsigned
universal group C_2 x D_8 of order sixteen. The coupled-completions
artifact gives reversible presentation reductions and all 24 product
checks; its forward inverse again reverses. Thus this change escapes
the abelian cube but still supplies no strict inverse. More generally,
every completion preserving the seed and its specified XOR fibers has
finite 2-group abelianization. That uniform statement constrains the
abelianization only; it does not prove that every completion is finite.
