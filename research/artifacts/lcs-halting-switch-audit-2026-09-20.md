# A finite marked seed cannot be the nonhalting switch

Date checked: 2026-09-20. This is a bounded obstruction audit, not a proof
of perfect-completeness RE hardness. No local code, build, matrix search,
or MSI computation was run. The elementary proof below is written
mathematics, not a Lean certificate.

Throughout, a group homomorphism to a tracial matrix ultraproduct means
a homomorphism into its unitary group.

## 1. Outcome and precise target

The Liu-based six-generator seed cannot be attached, even by an
existentially chosen marked homomorphism, on every nonhalting branch of a
computable family whose halting branch has quantum value one. This follows
from finite proof enumeration. It holds before any uniform gap is required.
The same obstruction covers a recursively enumerable library of finite
seeds and finite normal-closure combinations of their killed marks.

The desired strong endpoint is a computable family of finite binary LCS
games L_e and one s<1 with

```
e halts       ==> omega_q(L_e)=omega_qa(L_e)=1,
e never halts ==> omega_q(L_e)=omega_qa(L_e)<=s.
```

Here value one is a supremum over finite-dimensional strategies; it need
not be attained in a finite dimension. A perfect qa correlation exists
when that supremum is one. A perfect qc correlation only gives a tracial
model and is insufficient for the halting clause.

The obstruction is `lcs-switch-marked-seed-transport-is-re`. It does not
disprove the strong endpoint. It proves that one natural implementation
of its nonhalting clause is impossible.

## 2. Inputs, source verification, and existing boundaries

The specific seed (K,j) is
`leavitt-central-sign-seed-for-lcs`: K is finitely presented, j is a
nontrivial central involution, and every homomorphism from K to a tracial
matrix ultraproduct sends j to 1. This is the only analytic property the
argument uses. Its provenance remains **Jihao Liu**'s analytic theorem,
the reviewed Leavitt presentation and radical arguments, and the
**Paddock--Slofstra** central-tag construction. **Andreas Thom** retains
credit for the conditional normalization/double route; that route is not
reproved or required by the elementary obstruction.

The Liu PDF URL recorded by the seed audit returned an internal browser
error in this audit. Accordingly the seed property is consumed as the
explicit repository premise, not described as a fresh independent
verification of Liu's proof.

Primary sources checked on the date above:

- **Connor Paddock and William Slofstra**, [Satisfiability problems and
  algebras of boolean constraint system games](https://arxiv.org/html/2310.07901v2),
  Lemma 5.7: a linear system has an R^U model exactly when its solution-group
  sign survives approximate representations. Proposition 5.8 is the
  finite-presented nonhyperlinearity/LIN separation equivalence.
- **William Slofstra**, [Tsirelson's problem and an embedding theorem for
  groups arising from non-local games](https://arxiv.org/abs/1606.03140),
  the source of the existing constructive, central-sign-preserving
  solution-group embedding. Its exact algebraic statement is already
  recorded in `slofstra-solution-group-embedding-preserves-marked-involutions`.
- **Aviv Taller and Thomas Vidick**, [Approximating the quantum value of
  an LCS game is RE-hard](https://arxiv.org/html/2507.22444v2), introduction:
  their construction retains imperfect completeness and explains the
  separate algebraic obstacle to generic BCS-algebra embeddings.
- **Daniel Groves and Henry Wilton**, [Enumerating limit groups](https://ems.press/content/serial-article-files/29525),
  p. 392, footnote 1: enumeration of homomorphisms by generator words and
  finite relator proofs is standard. This is the only fact borrowed from
  that paper; no coherence conclusion is used. Its
  [corrigendum](https://arxiv.org/abs/1112.1223) was also located.

Repository searches and reads covered the weak constant compiler,
`lcs-compiler-target-is-goal-equivalent`, the existing reverse-Kleene
Taller--Vidick audit, `monotone-mf-switch-positive-branch-barrier`,
`arbitrary-forbidden-seed-hereditary-property-switch`, the FIN/INF
uniform-seed-map firewall, and the new Liu frontier audit. The new point
is different from the FIN/INF firewall: **no computably displayed seed
map, injectivity, or second-level index set is needed here**. Mere
existence of a mark-preserving map on coHALT is already too much.
The basic homomorphism enumeration is prior art; no originality claim is
made for that algorithm or elementary computability reasoning.

## 3. Exact theorem: existential seed maps are enough to fail

Fix a finite presentation K=<a_1,...,a_m | r_1,...,r_k> and a word j.
Assume every homomorphism from K to every tracial matrix ultraproduct
kills j. Let e map effectively to a finite presentation G_e and a
designated word J_e. Set

```
T = { e : there exists phi:K -> G_e with phi(j)=J_e }.
```

**Lemma.** T is recursively enumerable.

Enumerate all m-tuples u=(u_1,...,u_m) of words in the generators of
G_e. For each tuple, dovetail searches for derivations of the finitely
many equations

```
r_1(u)=1, ..., r_k(u)=1, j(u) J_e^-1=1
```

from the defining relators of G_e. Such a derivation is a finite product
of conjugates of defining relators or their inverses, followed by free
reduction. Its validity is decidable. Accept when all k+1 derivations
have been found. A successful tuple defines exactly the required
homomorphism. Every homomorphism has a word tuple and finite proofs of
these identities, so every element of T is eventually accepted. No word
problem oracle, injectivity test, or bound on the witnesses is used.

**Theorem.** There cannot be such a total computable family satisfying
both:

1. For each halting e, some homomorphism rho_e from G_e to a tracial
   matrix ultraproduct has rho_e(J_e)!=1.
2. For each nonhalting e, there exists phi_e:K->G_e with phi_e(j)=J_e.

For a halting e in T, rho_e composed with phi_e would be a homomorphism
from K that does not kill j, contradicting the seed premise. Thus T has
no halting indices. Clause 2 says T contains every nonhalting index.
Consequently T is exactly coHALT. The lemma makes coHALT recursively
enumerable. Dovetailing its recognizer with a simulation of e would
decide HALT, contradicting the standard diagonal argument: a machine
which halts exactly when that decider predicts that it does not halt
contradicts the prediction on its own code. This proves the theorem.

Apply it to the solution group of L_e. Perfect qa value gives the rho_e
in clause 1 (indeed it can send J_e to -1). Hence no such seed attachment
can underlie the desired halting-sensitive LCS family. The proof allows
arbitrarily long seed words chosen noncomputably on the negative branch;
enumerating all words defeats that attempted escape.

## 4. Stronger version: an enumerable library and normal closure

Let D be any recursively enumerable collection of pairs (K_i,j_i), each
K_i given by a finite presentation, and each j_i killed by every tracial
matrix-ultraproduct homomorphism. For a finitely presented G, define

```
N_D(G) = normal closure in G of
         { phi(j_i) : i in D and phi:K_i -> G a homomorphism }.
```

Membership J_e in N_D(G_e) is recursively enumerable uniformly in e.
A certificate consists of finitely many source indices, finitely many
generator substitutions and proofs of their source relators, conjugating
words v_l, signs epsilon_l, and a proof in G_e of

```
J_e = product_l v_l phi_l(j_(i_l))^epsilon_l v_l^-1.
```

All this is finite data. Dovetail the enumeration of source indices and
the finite derivation searches. Conversely membership in normal closure
always has such a finite expression. Every tracial matrix-ultraproduct
homomorphism of G_e kills N_D(G_e), by composition and normality of its
kernel. Thus if halting outputs have a model preserving J_e, membership
can never hold on a halting index. Requiring it on every nonhalting index
again enumerates coHALT and is impossible.

The fixed Liu seed is a singleton library. This version also rules out
finite products of conjugates of several transported seed marks and any
recursively enumerable library of certified bad finite seeds. It does
not assume a computable analytic modulus or a uniform filling bound.

In particular, if perfect-completeness RE hardness does hold, then for
every such library D some nonhalting output sign must lie outside
N_D(G_e), despite being killed in all tracial matrix-ultraproduct models.
So a successful proof must produce negative behavior that this finite
transport certificate language cannot exhaust.

## 5. Concrete failed switches

**Persist the seed, then append relations upon halting.** If the output
continues to receive the seed by a marked map, every output kills its
sign in every tracial matrix model, on either branch. Quotienting the
seed cannot restore that sign: composition with the quotient still kills
it. This is the HS analogue of the already recorded monotone MF barrier.
Killing the old j and naming an unrelated fresh J does not prove anything
about the fresh J.

**Attach the seed only when a control word is nontrivial.** Ordinary
Adian--Rabin style constructions may contain an unmarked bad subgroup
on one branch. That alone does not force the designated solution-group
sign to be killed. If an extra construction forces J to equal its seed
mark, or lie in the normal closure of finitely many transported marks,
the theorem above applies. Nontriviality of the control word does not
remove the finite certificate for the resulting marked equality.

**Select a tail copy after seeing the branch.** The FIN/INF recursive-ray
compiler avoids its own uniform-map obstruction by a noncomputable tail
cut. Here that is insufficient if the eventual finite output receives
the fixed finite source by a map taking j to the designated J. Such a
map still has a finite searchable tuple. An infinitely presented source
can evade the finite-relator enumeration step, but converting it to a
finite source/output with the required quantum models is precisely a
new obligation; Higman embedding alone supplies no positive model
extension theorem or uniform game gap.

## 6. The independent quantitative and game interfaces

For one fixed seed map phi:K->G, finite filling certificates give constants
A,B with the existing restriction estimate

```
kappa_(G,J)(delta) <= kappa_(K,j)(A delta)+B delta.
```

This transfers a qualitative killed-mark property for that fixed output.
Across a family, A and B can grow, and the conversion from game loss to
maximum relator defect also depends on the probabilities of the checks.
Pointwise positive gaps therefore supply no uniform s<1.

There is an elementary concrete dilution example. Take one fixed LCS
game L_* with omega_q(L_*)<1. Make L_n choose its checks with probability
1/n and an independent perfectly satisfiable linear-system component
with probability 1-1/n, with disjoint variable names. Component questions
identify the branch. Restricting any strategy gives the upper bound, and
tensoring a near-optimal L_* strategy with a perfect dummy strategy gives
the reverse bound. Thus

```
omega_q(L_n)=1-(1-omega_q(L_*))/n.
```

Every L_n still carries the bad seed obstruction and has strict gap, but
the gaps tend to zero. Rational check weights can be implemented directly
or by repeated checks. This example diagnoses the gap quantifier; it is
not a halting reduction.

For a proposed group-to-LCS approach, three obligations remain separate:

1. Halting must produce a model of the **output** with sign -1, or
   asymptotic models whose sign survives. Algebraic nontriviality gives
   only qc completeness. An exact group embedding by itself does not
   assert extension of source finite-dimensional or approximate models.
2. Nonhalting must give a dimension-independent defect obstruction by a
   mechanism outside the finite marked-seed transport class above.
3. One must propagate it through the actual output tests to a constant
   loss independent of e, and meet any polynomial-time requirement of
   the intended complexity statement.

No one of these is supplied by choosing the fixed separating game on all
inputs. The existing weak compiler remains valid on its stated qc/qa
promises; it carries no halting distinction. Liu's new negative input
settles that constant-separation endpoint but does not repair the
Taller--Vidick perfect quantum completeness seam.
