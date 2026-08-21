---
rg: 2
id: linear-encoding-lcs-admits-odd-subset-cheats
kind: claim
title: Every LCS built from a linear encoding of a constraint system is also solved by the odd-subset relaxation
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  central-pinning-forbids-nonlinear-predicates: that is finite-group character theory about one pinned sector; this is about arbitrary LCS constraints on encoded variables and identifies the complete family of extra solutions that perfect completeness lets in.
  taller-vidick-lcs-re-hardness: that is a theorem with noisy completeness; this explains, without noise, which cheating solutions any noise-free linear test must tolerate.
---

Let `B` be a boolean constraint system with contexts `C`, satisfying sets
`S_C`, and shared variables.  Let `L` be any binary LCS whose variables
are `a_(C,phi)` indexed by functions `phi : S_C -> {+1,-1}` (any subset of
such functions, for any contexts), with the honest encoding of a context
assignment `x in S_C` being `a_(C,phi) = phi(x)`.  Suppose every
constraint of `L`, of the form `prod a_(C_i,phi_i) = J^eps`, is satisfied
by every honest encoding of every solution of `B` (in particular by all
consistent tuples of context assignments).  Then `L` is also satisfied by
every **odd-subset assignment**

```text
a_(C,phi) = prod_(s in T_C) phi(s),     T_C subseteq S_C,  |T_C| odd,  (OS1)
```

whenever the sets `T_C` have consistent mod-2 marginals on shared
variables: for each function `psi` of the shared variables of `C, C'`,
`prod_(s in T_C) psi(s|_shared) = prod_(s' in T_(C')) psi(s'|_shared)`.
In particular, within one context the classical solutions of the linear
long-code constraints `a_phi a_psi = a_(phi psi)`, `a_(-1) = J` are exactly
the characters `chi_T` with `|T|` odd, and in a representation with
`J = -I` every exact solution is a projection-valued mixture of odd-subset
characters.

*Proof.*  Fix a constraint `prod_i a_(C_i,phi_i) = J^eps` and group its
factors by context: `A_C(s) := prod_(i : C_i = C) phi_i(s)`.  Honest
satisfaction for all consistent tuples says `prod_C A_C(x_C) = (-1)^eps`
for all consistent `(x_C)`.  For an odd-subset assignment the left side is
`prod_C prod_(s in T_C) A_C(s)`.  If the constraint involves one context,
`A_C` is the constant `(-1)^eps` on `S_C`, and an odd product of it is
`(-1)^eps`.  If it involves several contexts, honest satisfaction for all
consistent tuples forces each `A_C` to factor through the shared
variables up to a constant, and the consistent-marginal hypothesis makes
the odd products agree.  The within-context statement is the
classification of characters of `(Z_2)^(S_C)` with `chi(-1) = -1`.

**Consequence.**  A noise-free LCS compiler with perfect completeness
(`perfect-completeness-constant-soundness-lcs-compiler`) can be sound only
if the **odd-subset relaxation** of the source constraint system, whose
solutions are consistent families of odd subsets rather than of points,
is itself robustly unsatisfiable in finite dimensions.  Classically this
relaxation is a linear system over `F_2` and is why Hastad's 3-XOR test
needs noise; the Taller--Vidick mask is the quantum instance of that
necessity.  The perfect-completeness target is therefore not "remove the
noise from the decoder" but "choose a source whose odd-subset relaxation
is still hard", which is a statement about the constraint system and is
where a self-similar or self-reducing source could enter: a family whose
odd-subset relaxation is again an instance of the family would make the
relaxation's soundness follow from the family's.
