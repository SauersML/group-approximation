---
rg: 2
id: every-bcs-is-a-trace-pullback-quotient-of-an-lcs
kind: claim
title: Every finite BCS is a trace-pullback quotient of a finite LCS
distinct_from:
  non-ce-trace-on-sofic-racg: that places the fixed non-CE trace on a tame right-angled Coxeter group; this identifies that Coxeter algebra as an actual finite LCS solution algebra and audits the unital quotient direction.
  trace-extending-bcs-to-lcs-maps-are-already-terminal: that requires a unital arrow from the BCS algebra into the LCS algebra; this constructs the reverse arrow and proves by an exact countermodel that it has no soundness content.
  property-t-trace-envelope-has-rigid-coequalizers: that gives a nonamenable trace-extending inclusion and rules out faithful quotients afterward; this shows that trace pullback along an LCS-to-BCS quotient is universally available before GNS reduction.
---

**ESTABLISHED MAP-DIRECTION FIREWALL.** Let `B` be a finite Boolean constraint system whose algebra is nonzero
(in particular, any finite BCS carrying a tracial state). There is an explicit finite binary LCS `L_B) and a
unital surjective star-homomorphism

```text
q:A_(L_B)->A_B.                                         (LBQ1)
```

For every specified tracial state `tau` on `A_B),

```text
tau_L=tau after q                                      (LBQ2)
```

is a tracial state on the LCS algebra. If `tau` is non-Connes-embeddable,
then `tau_L` is non-Connes-embeddable and the two trace-GNS von Neumann
algebras are canonically isomorphic.

Nevertheless `L_B` has a one-dimensional perfect representation, and
its solution group is residually finite. Thus `A_(L_B)` is
`R^U)-satisfiable and its solution group is hyperlinear even when
`tau_L` is non-CE.

The construction is concrete. Let `W_B` be the right-angled Coxeter
group with one involution `s_x` for every BCS variable and with
`[s_x,s_y]=1` whenever `x,y` occur in a common context. For every such
pair introduce an LCS ancilla `a_(x,y)` and the parity-zero row

```text
x+y+a_(x,y)=0.                                         (LBQ3)
```

Then the solution group is

```text
Gamma_(L_B) isomorphic to W_B times <J>,                (LBQ4)
```

where `J` is the central solution-group involution, and its negative
central-sign solution algebra is

```text
p_- C*(Gamma_(L_B)) p_- isomorphic to C*(W_B),
p_-=(1-J)/2.                                            (LBQ5)
```

The BCS symmetries satisfy all Coxeter commutations, so imposing the
forbidden spectral-projection relations gives (LBQ1).

This proves that an LCS-to-BCS quotient carrying a chosen non-CE trace is
not a partial solution of the perfect-completeness gate: such a quotient
exists for every finite BCS with nonzero algebra, including completely
classical ones. The
load-bearing map must run from the no-`R^U` BCS algebra into the LCS
algebra and carry an extending trace, or otherwise exclude **every**
Connes-embeddable LCS trace. Existence of one pathological trace on an LCS
algebra says nothing about hyperlinearity of its solution group.

DERIVATION
lcs-coxeter-cover-and-trace-pullback-proof
