# From Liu's analytic theorem to binary linear games: exact scope and first explicit seed

Checked September 20, 2026. This note separates a consequence already
obtained by composing named theorems, an elementary quantitative bridge,
and the still missing numerical game certificate. No local code, build,
dimension search, or game enumeration was run for this audit.

## 1. Source gate and attribution

Primary sources checked:

- Connor Paddock and William Slofstra, [Satisfiability problems and algebras
  of boolean constraint system games](https://arxiv.org/html/2310.07901v2),
  Theorem 3.11, Lemma 5.7, Proposition 5.8.
- Aviv Taller and Thomas Vidick, [Approximating the quantum value of an LCS
  game is RE-hard](https://arxiv.org/html/2507.22444v2), introduction and
  Lemma 4.2, especially the explicit discussion of imperfect completeness.
- William Slofstra, [Tsirelson's problem and an embedding theorem for groups
  arising from non-local games](https://arxiv.org/abs/1606.03140), Theorem
  3.1 and the constructive embedding already imported in Cairn.

Paddock--Slofstra Proposition 5.8 is genuinely about binary LINEAR systems,
not only arbitrary Boolean constraint systems. The consequence is a qc/qa
separation, not only qc/q nonattainment. The theorem-level claims in the
user's supplied quantum-information comparison are correct with these
qualifications. The reviewed published reductions retain their authorship.

Our new negative-group input ultimately uses **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2/6.7, via the separately documented Leavitt arguments. The
normalization route credits **Andreas Thom** for the conditional theorem.
The abstract finite-presentation route separately imports **Huynh Viet
Khanh**. The concrete presentation route instead retains all dependencies
of the reviewed Thompson--Steinberg presentation. These game deductions do
not independently verify Liu's analytic proof and are not Lean certificates.

## 2. The immediate consequence and the gap quantifier

The existing graph already has the Leavitt nonhyperlinearity and finite
presentation claims. Apply the Paddock--Slofstra equivalence to that same
group. Its output is a finite binary system Ax=b whose BCS algebra has a
tracial state but no homomorphism into R^U. The game dictionary converts
this to a perfect commuting strategy and no perfect quantum-approximable
strategy.

Here is the elementary extra compactness argument, stated independently of
the source's theorem text. Fix a distribution assigning positive probability
to every tested question pair. For a finite game, correlations are vectors
in a finite cube. Their quantum-approximable set is the closed closure of
the finite-dimensional quantum correlations, hence compact. Winning
probability is a continuous linear function. If its maximum were one, the
maximizing correlation would lose on no tested pair, because all question
weights are positive. That would be a forbidden perfect qa strategy.
Consequently its maximum is 1-epsilon for some epsilon>0. The supremum
over finite-dimensional strategies equals that same maximum over the
closure. This proves a positive all-dimensions gap, without assigning a
number to epsilon.

The new node is `binary-lcs-perfect-qc-strict-qa-gap-exists`. The source
equivalence and game dictionary are published reductions, not new Cairn
mechanisms. This is also not a new refutation of Connes embedding or the
general qc/qa equality: MIP*=RE already settled those broader questions.
The additional restriction here is parity/linear constraint syntax.

## 3. An explicit central-tag construction, with modulus

Suppose a finite presentation G=<S|R> and a word w are given, with w!=1
and every tracial matrix-ultraproduct homomorphism killing w. This input is
stronger than merely being handed a presentation labelled nonhyperlinear:
the marked word and its nontriviality proof must be present.

Take G_1*G_2 and v=w_1w_2. Free-product normal form shows that every
positive power of v is a nonempty reduced word, so v has infinite order.
Let B=(G_1*G_2) times <J|J^2=1>. Then <v,J> is Z times C2. Its map

```
v -> vJ,  J -> J
```

is an automorphism (its square is the identity). Adjoin a stable letter
implementing this automorphism. The resulting finite presentation is

```
K=<S_1,S_2,J,t | R_1,R_2,J^2,[J,s] for all s,
                       [t,J], t v t^-1 (vJ)^-1>.
```

Britton's lemma embeds B in K. Hence J!=1; its listed commutators make it
central in K, not only central in B. Every matrix-ultraproduct map kills
w_1 and w_2, hence v; the HNN relation then kills J.

For finite-dimensional unitary tuples, use maximum normalized-HS relator
defect and write

```
kappa_G(delta) = sup ||w(U)-I||_2 over all dimensions and
                 all U with source relator defect <= delta.
```

Its limit at zero is zero: a contrary sequence would produce a tracial
matrix-ultraproduct homomorphism preserving a positive distance for w.
Restrictions of a delta-representation of K to both source copies have
source defect at most delta. Unitary invariance and the triangle inequality
give

```
||v-I||_2 <= ||w_1-I||_2 + ||w_2-I||_2 <= 2 kappa_G(delta),
||J-I||_2 <= ||vJ-tvt^-1||_2 + ||tvt^-1-v||_2
           <= delta + 2 ||v-I||_2
           <= delta + 4 kappa_G(delta).
```

This proves `central-hnn-tag-transfers-hyperlinear-radical` with no hidden
dimension-dependent normalization. It is the standard marked HNN idea,
with its centrality and quantitative bookkeeping exposed.

**Presentation caution.** The displayed HNN presentation in the web text
of Paddock--Slofstra Proposition 5.8 does not explicitly list [t,J]. We
make no claim here about whether surrounding group-over-C2 conventions
supply it implicitly. Our route includes it and realizes an HNN extension
over the full subgroup <v,J>, which proves centrality and injectivity
directly. No inference in Cairn relies on centrality in a base implying
centrality after an arbitrary HNN extension.

## 4. First constructive checkpoint: six generators, twenty-five relators

Use the source in `thompson-steinberg-presentation-of-leavitt-unit-group`.
Its complete eighteen literal relator words are already stored in
`experiments/nonsofic-certificates/presentations/thompson-steinberg-presentation.json`.
Its named generators are a,b,c,x and its reviewed identification sends

```
x -> 1 + S[00]T[01].
```

Put q=S[00]T[01]. Then q^2=0 by disjoint-prefix cancellation, and
T[00]qS[01]=1, so q!=0. In characteristic two, x is therefore a
nonidentity involution. The whole-group radical theorem
`binary-leavitt-tracial-ultraproduct-images-are-trivial` kills this literal
generator in all tracial matrix models. No word search translating the
rank-four compression element is needed.

Because x is already an involution, use the smaller involutive tag. In
G times C2, the subgroup <x,J> is C2 times C2, and x -> xJ,J -> J is an
automorphism. Its HNN extension preserves the base and central J by the
same argument as above. The tag gives exactly six generators and
twenty-five relators: eighteen source relators, J^2, four commutators
with J, [t,J], and

```
t x t^-1 J^-1 x^-1.
```

This is a specified finite presentation and source word suitable for the
existing effective Slofstra embedding. It is recorded as
`leavitt-central-sign-seed-for-lcs`. It is NOT a claimed size bound for the
eventual game. The twenty-five-relator seed still inherits the reviewed
source completeness dependencies, including its stated Bleak--Quick
normal-closure input; merely checking source relators in a ring would not
be enough to identify the presented group.

## 5. Quantitative interface through the solution-group embedding

The existing `marked-approximate-radical-survives-solution-group-embedding`
and its route supply the following. Given fixed embedding words, let A be
the largest filling area of a substituted source relator and B the filling
area of the equality identifying the source sign with the output sign.
Then

```
kappa_output,J(delta) <= kappa_K,J(A delta)+B delta
                       <= 4 kappa_G(A delta)+(A+B)delta.
```

For the smaller involutive Leavitt seed, the factor four improves to two:
the HNN estimate uses ||x-I||_2 directly instead of the doubled word.
Thus its output bound is 2 kappa_G(A delta)+(A+B)delta.

The areas are finite, and the constructive embedding can output finite
certificates for the finitely many substituted identities. These are
ordinary finite word certificates, not approximate-representation
enumerations or a word-problem oracle. The estimate is dimension-free.

Thus the first remaining tasks are now specific:

1. Emit the wagon-wheel hypergraph, binary matrix A and vector b, along
   with the finite embedding/filling manifest for the specified seed.
2. Extract an explicit numerical source bound kappa_G(eta)<=c for a useful
   c<1/2, controlling the analytic constants upstream of Liu's theorem.
3. Fix one game convention and quantify its near-perfect-strategy to
   approximate-solution-group conversion, propagating the source bound to
   a rational loss epsilon>0.

No numeric certificate for steps 2-3 has been produced. Compactness alone
does not give an implemented terminating search or an efficient constant.
Bounded matrix-dimension experiments cannot certify a gap in all dimensions.
The OPEN target `leavitt-lcs-game-with-certified-numerical-gap` records
these obligations. The old `explicit-exact-support-lcs-witness` is a
different construction-specific demand and is not silently closed.

## 6. Further wiring without overclaiming

The existing graph-isomorphism bridge sends the separating LCS to the CFI
pair G_(A,b),G_(A,0), with a perfect qc but no perfect qa isomorphism.
The new route only feeds the established LCS endpoint into that existing
AMRSSV/BCEHPSW theorem; those authors retain attribution.

There is a subtle old target in Cairn called
`perfect-completeness-constant-soundness-lcs-compiler`. Its actual promises
are perfect COMMUTING completeness on halting inputs and strict QUANTUM
soundness on nonhalting inputs. A constant map to our single separating
game satisfies both promises, independently of whether its input machine
halts. The new route closes that weak interface exactly as written. It
does not prove a useful halting reduction or LIN-MIPstar_(1,s)=RE. In the
latter claim the halting side requires perfect quantum completeness, and
our fixed game has no such strategy.

Taller--Vidick's current v2 source retains imperfect completeness. Their
positive-noise test and its Fourier decoder do not become perfect by
plugging in a fixed qc-only seed. Existing no-go nodes concerning the
opposite-sign mask pair are not refuted by the new existence theorem.
Likewise no generic exact BCS-algebra-to-LCS embedding is supplied.

One more useful boundary: the output solution group itself has a central
nontrivial hyperlinear-radical involution. The existing conditional theorem
`perfect-lcs-gap-implies-weak-non-mf` therefore makes that output non-MF
by finite-sign-sector renormalization. It need not share the MF property
of a different negative seed such as the symmetric double. The HNN and
solution-group constructions do not claim to preserve MF.
