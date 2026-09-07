---
rg: 2
id: certificate-linear-automata-have-local-linear-decoders
kind: claim
title: Injective certificate-controlled linear automata admit certificate-local linear left inverses
distinct_from:
  certificate-controlled-routing-is-surjunctive: that treats one input read per output and proves surjectivity; this permits arbitrary finite linear combinations and constructs a left inverse without claiming surjectivity.
  stable-finiteness-failure-refutes-surjunctivity: that dualizes a given inverse pair with constant group-algebra coefficients; this obtains a local inverse from injectivity of a certificate-dependent family.
---

Let k be a finite field, B a nonempty finite alphabet, and G any group.
Suppose E on (k^n x B)^G is a cellular automaton of the form

    E(x,c)=(T_c x,c),

where T_c is k-linear in x and its finite local rule depends on a finite
pattern of c. If E is injective, there is a cellular automaton

    D(y,c)=(S_c y,c)

with the same type of certificate-local, data-linear rule and

    S_c T_c=I for every c in B^G.

No assumption of surjunctivity, soficity, amenability, or a decidable word
problem is used. The finite memory of S is not asserted to have a computable
bound in the memory of T. This is an existence and finite-description
lemma, not a construction of an injective nonsurjective E.

It is a parameter-local form of the familiar left-inverse phenomenon for
stably injective linear nonuniform cellular automata. Compare Phung,
*On linear non-uniform cellular automata: duality and dynamics*,
Theorem 10.1, https://arxiv.org/abs/2208.13069. The route proves the
continuous dependence on the certificate directly.
