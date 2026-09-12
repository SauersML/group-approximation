---
rg: 2
id: boone-higman-via-shell-germ-stabilizers
kind: route
title: Build a universal Cantor shell action and discharge the three local finite-presentation clauses
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - shell-cantor-embeddings-are-finite-germ-extensions
  - contracting-srn-rational-stabilizers-are-fp
  - decidable-inputs-have-fp-shell-stabilizers
  - twisted-brin-thompson-finite-presentation-criterion
artifacts:
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
---

This route remains conditional on the named OPEN shell-stabilizer
construction. The deduction from that hypothesis is as follows.

Given a finitely generated group G with decidable word problem,
Clapham gives an embedding in a finitely presented group P_0 with
decidable word problem. Put P=P_0 times Z. It is infinite, finitely
presented, and has decidable word problem. Apply the open hypothesis
to P and let E=E_nu be its Cantor shell group.

## Finite presentation of E

The shell construction proves that E is a finite germ extension of
B=V with singular set Omega=V*p. V acts highly transitively on Omega:
restrict finitely many desired prefix maps to disjoint small cones
and complete the finite partial table. Thus it has finitely many
orbits on Omega^2.

For M subset M' subset Omega, put

    S(M,M')={e in E: sing(e) subset M and e fixes M' pointwise}.

If |M'|<=2 and M is nonempty, high transitivity identifies S(M,M')
by V conjugation with one of the three groups A_1,A_12,A_2 in the
open hypothesis. When M is empty it is the pointwise stabilizer
Fix_V(M'). These groups are finitely presented by the rational-set
stabilizer claim applied to the trivial self-similar coefficient
group and the binary alphabet; the empty case is V itself.

Every S(M,M') required at n=2 is therefore finitely presented.
[Belk--Hyde--Matucci, Theorem 2.1](https://arxiv.org/html/2407.03149v1#S2.SS1)
now proves E finitely presented.

## Finite generation of point stabilizers

Fix r in Omega and write E_r=Stab_E(r), B_r=Stab_V(r). The
restriction E_r is a finite germ extension of B_r with the same
singular set Omega. To justify this, a local V representative of
an E_r germ can be corrected on r by a V map equal to the identity
near the image of the germ's basepoint. A representative with one
singularity can be corrected in the same way. If the basepoint is
r, it is already fixed and requires no correction. Disjoint-cone
prefix interpolation realizes the correction. Conversely locally
B_r implies locally V, and an element of E_r lying in V is in B_r.
Conjugated shell elements, followed by the same correction, realize
a nontrivial singularity at each point of Omega.

B_r has two orbits on Omega, namely {r} and its complement. For
M subset M' with |M'|<=1, the groups required by Theorem 2.1 at
n=1 for E_r are exactly

    S(M,M' union {r}).

Their second argument has size at most two. They are finitely
presented, and hence finitely generated, by the preceding paragraph
and the open hypothesis. The n=1 theorem proves E_r finitely generated.
Only finite generation is needed here; no third-point hypothesis
has been added to the construction problem.

## The final envelope and the unresolved clause

E acts faithfully on the dense set Omega and is highly transitive
because V is a subgroup. It is finitely presented and its point
stabilizers are finitely generated. The twisted Brin--Thompson
criterion therefore supplies a finitely presented simple group
Omega V_E containing E, hence P and G.

The proof does not require the shell generators to be rational or
finite state. That is essential in view of the complexity obstruction
to a universal rational realization. It also does not use a quotient
of (E)_p by (V)_p: the prefix germ is not normal, as recorded in
`shell-prefix-germ-is-not-normal-or-finite-index`. The unresolved
work is exactly to choose nu and prove finite presentation of the
three specified groups, with the original P embedded faithfully.
