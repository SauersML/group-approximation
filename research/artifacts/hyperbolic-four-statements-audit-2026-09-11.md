# Four hyperbolic existence statements: complete reductions and the MF gap

Audit date: 2026-09-11. Three parallel proof audits checked the Dehn filling,
Kazhdan quotient, and MF branches. The requested four-way equivalence is
**not established by the available proof**. The first three statements are
equivalent; the fourth implies all three. The missing direction is from a
non-residually-finite hyperbolic group to a non-MF hyperbolic group.

This distinction concerns the proof of equivalence, not a construction of a
counterexample. No existential assertion below is established here.

## 1. Statements and certified directions

Write:

- A: some word-hyperbolic group is not residually finite;
- B: some word-hyperbolic group is not virtually torsion-free;
- C: some infinite word-hyperbolic Kazhdan group has no nontrivial finite quotient;
- D: some word-hyperbolic group is not operator MF.

Operator MF means a group embedding into the unitary group of a norm matrix
corona `product_n M_(d_n)(C) / direct_sum_n M_(d_n)(C)`, with the direct sum
consisting of sequences whose operator norms tend to zero. It does not mean
quasidiagonality or require completely positive coordinate maps.

| Direction | Proof and status |
| --- | --- |
| A implies B | Complete: put an infinite-order residual element into a maximal elementary peripheral subgroup and fill a sufficiently deep normal cyclic subgroup; the residual-torsion case is immediate. |
| B implies A | Complete: finite conjugacy classes of finite subgroups allow finitely many separating finite quotients to produce a torsion-free normal subgroup of finite index. |
| A implies C | Complete: make a free subgroup in a finite residual, apply Olshanskii, then take a hyperbolic common quotient with a Kazhdan partner. |
| C implies A | Complete: every nonidentity element is invisible to every finite quotient. |
| D implies A | Complete: residually finite groups have separating exact finite-dimensional unitary representations. |
| C implies D | The former proof has an unsupported MF-to-weak-quasidiagonality passage. No replacement proof found. |

Thus the established result is `D implies (A iff B iff C)`, understood as
`A iff B iff C` together with `D implies A`. The four-way target remains open
in Cairn; it is not refuted.

## 2. Full group-theoretic proofs

The complete Osin proof is in
[the filling artifact](hyperbolic-rf-vtf-osin-full-proof-2026-09-11.md).
For a residual element `g` of infinite order, choose `k>=1` with
`<g^k>` normal and finite index in its maximal elementary subgroup `E(g)`.
For all sufficiently large `j`, Osin's theorem embeds
`E(g)/<g^(kj)>` into `Q_j=G/normal_closure(g^(kj))`. This peripheral quotient
is finite, so `Q_j` is word-hyperbolic. The image of `g` has exact order
`kj>1`, and all its finite images remain trivial. Every subgroup of finite
index contains the finite residual, so `Q_j` is not virtually torsion-free.
The artifact also proves the torsion case and the converse.

The complete quotientless/Kazhdan proof is in
[the common-quotient artifact](hyperbolic-quotientless-kazhdan-proof-2026-09-11.md).
It includes both a direct Olshanskii reduction from one invisible element
and exact finite-radical and Bass--Serre checks for the Kazhdan common
quotient. The output remains word-hyperbolic, not merely acylindrically
hyperbolic. The equivalence predates this audit: Kapovich--Wise,
*The equivalence of some residual properties of word-hyperbolic groups*,
J. Algebra 223 (2000), Theorems 1.2 and 5.1, covers the finite-quotient and
virtual-torsion-freeness questions. The Osin argument is an alternative proof.

## 3. Full proof that D implies A

Let `G` be countable and residually finite. Enumerate its nonidentity
elements as `g_1,g_2,...`; for a finite group use repetitions or a finite
product. For each `i` choose a homomorphism `q_i:G->F_i` to a finite group
such that `q_i(g_i)!=1`. Let `q^(n):G->F_1 x ... x F_n` be their product and
let `u_n` be its composition with the left regular representation of the
finite product on a finite-dimensional complex Hilbert space.

Each `u_n` is an exact unitary representation. For `n>=i`, the permutation
`u_n(g_i)` moves the basis vector at the identity to an orthogonal vector,
so `||u_n(g_i)-1||>=sqrt(2)`. Therefore

```text
g |-> [(u_n(g))_n]
```

is a homomorphism to the unitary group of the norm matrix corona and has
trivial kernel. The trivial group has the trivial embedding. Thus every
countable residually finite group is operator MF. Word-hyperbolic groups
are finitely generated and countable, so a non-MF one cannot be residually
finite. Combining with Section 2 proves that D implies B and C as well.

## 4. Why the previous MF step cannot be certified

The previous route cited Dadarlat's *Obstructions to matricial stability of
discrete groups and almost flat K-theory*,
[arXiv:2007.12655v2](https://arxiv.org/html/2007.12655v2), Definition 3.10 and
Proposition 3.19. That proposition, attributed to Ozawa--Thom, concerns
**weakly quasidiagonal** Kazhdan groups. Weak quasidiagonality requires
separating asymptotically multiplicative **unital completely positive**
maps from the full group C*-algebra to matrix algebras. An MF embedding
only supplies asymptotic unitary maps on the group. The coordinate maps
need not extend completely positively.

The introduction does print the arrow used by the old proof. The definitions
do not prove that arrow: polar decomposition proves the reverse implication,
from weak quasidiagonality to MF. [The detailed source audit](operator-mf-weak-quasidiagonality-audit-2026-09-11.md) records the
unsupported passage and the valid non-weak-quasidiagonal conclusion.
Neither the appearance of that arrow nor finding a gap is a counterexample
to the proposed MF conclusion. The corresponding claim must remain open.

Two plausible repairs also need extra hypotheses:

- Local lifting for the **full** group C*-algebra can produce the missing
  completely positive maps. Willett,
  [arXiv:2408.13350](https://arxiv.org/pdf/2408.13350), Proposition 2.7,
  explicitly assumes weak matricial LLP for this approximation step.
- Local operator-norm matrix stability can turn MF into quasidiagonality;
  Dadarlat, [*Non-stable groups*](https://www.math.purdue.edu/~mdd/Webpapers/f-hyper-rev.pdf),
  Lemma 5.10 and Theorem 5.15, explicitly require stability in that argument.

The quotient construction proves neither hypothesis. Exactness of a
hyperbolic group concerns its reduced group C*-algebra; it supplies no such
lifting theorem for its full group C*-algebra. Finite presentation likewise
does not by itself make approximate matrix relations stable. Adding either
hypothesis without a proof would only conceal the missing implication.

## 5. Trust and verification boundary

The new three-way equivalence is a Cairn theorem with complete ordinary
mathematical deductions and explicit literature inputs. The geometric and
operator-algebra literature theorems have not been formalized in Lean here.
Cairn checks graph integrity and dependency closure; it does not check the
mathematical truth of a prose proof. In particular it must not treat the
MF bridge as established merely because a citation route has no prerequisites.
