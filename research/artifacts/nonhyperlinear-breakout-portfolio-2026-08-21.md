# Cairn Breakthrough Memo: New Routes Toward an Explicit Non-Hyperlinear Group

**Date:** 2026-08-21  
**Scope:** deliberately outside the current Cairn local minima  
**Integration status:** imported in full on 2026-08-21. The graph wiring uses
the current repository rather than the older snapshot against which the memo
was drafted, so nearby later nodes are cross-referenced instead of duplicated.

---

## 0. Executive conclusion

The current Cairn program has already discovered the central strategic fact:
the successful non-MF mechanism does **not** transfer to normalized
Hilbert--Schmidt geometry by replacing operator norm with `||.||_2`. The
flagship non-MF group is explicitly sofic, hence hyperlinear. The remaining
problem is not "find a sharper rank count" in the same proof. It is to
introduce a mechanism that either:

1. converts a regular-trace microstate into a **different, more rigid object**
   on which normalized-HS errors become macroscopic; or
2. avoids matrix-stability altogether by placing an already
   non-Connes-embeddable von Neumann algebra inside the **canonical group
   factor** of a newly constructed group.

After auditing the supplied graph (`cairn status`, `frontier`, `context`, and
targeted searches), the most promising genuinely new idea is:

> **Projectivize the relative-commutant problem and lift the stable letter to
> its inner superoperator `Ad(T)`.**
>
> Cairn currently tries to prove that a stable-letter matrix `T` centralizing
> a co-dense subgroup `C` must centralize the ambient group `A`. That is
> stronger than necessary. To kill a regular microstate it is enough to prove
> that `[T,a]` is **scalar**. Passing to `Ad(T) in U(d^2)` quotients out
> exactly those scalars and turns `T` into a full-rank unitary superoperator.
> The regular trace then supplies a built-in constant gap: for a nontrivial
> word `w`, `|tr(w)| -> 0`, whereas a scalar commutator has
> `|tr(w)| = 1`.

This is not ordinary RCC, not flexible HS-stability, and not the existing
positive-density commutant theorem. It asks for a **projective/inner-
superoperator transfer theorem**, a materially weaker target that
automatically ignores the scalar cocycles responsible for many stability
obstructions.

Three other routes look high-leverage enough to pursue in parallel:

- **PI-degree curvature:** use fixed-degree polynomial identities to
  distinguish a genuine `M_r` source packet from the rectangular `M_(r^2)`
  escape. This attacks the exact "same reservoir" obstruction with a
  finite-matrix invariant that external multiplicity cannot counterfeit.
- **Double-centralizer reservoir locking:** physically occupy the would-be
  multiplicity reservoir with a second transverse finite packet. If the two
  packets are approximate mutual commutants on one recovered corner,
  rectangular relabeling has nowhere to hide.
- **Algebraic-relation compiler:** bypass HS stability completely. Embed a
  known non-CE relation algebra into a crossed product by an **algebraic
  compact abelian action**. Fourier duality then turns that crossed product
  into a group von Neumann algebra, producing a non-hyperlinear group
  directly.

The rest of this memo makes these and several more speculative routes precise,
gives conditional proof skeletons, and states the fastest falsification test
for each.

---

## 1. What the Cairn snapshot says must not be retried

The inspected graph has the top-level goal `non-hyperlinear-group` open, with
a very large frontier. The important point is not the number of frontier
nodes but the concentration of many of them around the same few bottlenecks.

### 1.1 The non-MF witness itself cannot become the hyperlinear witness

The supplied README explicitly records that the main non-MF group is sofic and
hence hyperlinear. The differential audit also records an explicit
Connes-embeddable representation of the literal non-MF mark. Therefore a route
of the form

```text
"prove the same marked word dies in every tracial representation"
```

is false for the existing witness.

### 1.2 Trace is refinement-blind

The operator-norm proof pays for compression by dimension loss. Normalized
trace does not see the same loss because external multiplicity can refill the
missing rank. This is the source of the rectangular countermodel repeatedly
found in the affine-Leavitt/Steinberg branches.

Any proposed invariant must therefore pass an **amplification firewall**:

```text
X |-> X tensor I_m
```

must not destroy the obstruction.

### 1.3 Sparse outliers defeat ordinary property-(T) spectral-gap arguments

Cairn has already proved a strong positive-density no-growth theorem in the
normalized adjoint space. It still cannot exclude an exceptional mode of
vanishing `d^2`-density. Re-proving "property (T) controls almost-invariant
vectors" will not close RCC: an exactly `C`-fixed vector is allowed to exist.

### 1.4 Full RCC is too ambitious if the mark only needs a trace gap

The current HNN route targets

```text
pi(C)' cap M = pi(A)' cap M.
```

But to contradict the regular character of `[t,a]`, equality of commutants is
unnecessary. A projective conclusion is enough. This observation is the
opening for Route I below.

### 1.5 The current "same reservoir" problem is real

The explicit rectangular model in the affine-Leavitt audit shows that merely
comparing source and target packet sizes is insufficient. A successful
argument must identify a basis-free invariant of the **matrix-factor degree**,
or must physically pin the multiplicity algebra so that it cannot exchange
roles with the label algebra.

### 1.6 Naive Pinsker/free-product arguments have a built-in RAAG counterexample

Recent asymptotic-freeness/Pinsker theorems are tempting, but one must not
apply them to an arbitrary embedding of free Haar unitaries into a matrix
ultraproduct. The right-angled Artin group on a four-vertex path contains free
endpoint generators and an infinite commuting chain between them, yet it is
residually finite and hyperlinear. Therefore any "free endpoints + commuting
chain is impossible in a matrix ultraproduct" theorem is false without an
additional **embedding-genericity** hypothesis.

That counterexample will be used below as a firewall, not ignored.

---

## 2. Scorecard

| Route | Core new invariant | Main blocker bypassed | Hard new theorem | Payoff | Priority |
|---|---|---|---|---|---|
| I. Projective RCC via inner superoperators | `Ad(U)`, trace-square distance | sparse RCC outlier; scalar cocycles | projective commutant transfer | explicit HNN non-hyperlinear group | **A+** |
| II. Projective HS-stability in `PU(d)` | phase-quotiented stability | ordinary property-(T) HS-instability | relative flexible stability modulo scalars | reuses arithmetic co-density | **A** |
| III. PI-degree curvature | Amitsur--Levitzki/central polynomial degree | rectangular reservoir escape | positive-density PI bridge | closes affine/atlas packet route without rank bookkeeping | **A+** |
| IV. Double-centralizer reservoir lock | mutual commutants / finite commuting square | label-multiplicity role swap | common-corner bicommutant extraction | direct same-reservoir theorem | **A** |
| V. Algebraic relation envelope | Pontryagin duality | all HS stability | non-CE relation inside algebraic free action | non-hyperlinear semidirect product | **A+** |
| VI. Haar linear-subshift compiler | finite-field algebraic process | ZPC/LCS robust microstate soundness | non-CE algebraic crossed product | highly explicit recursively presented group | **A** |
| VII. Embedding-lock + Pinsker collision | 1-bounded entropy / unique embedding position | pointwise RCC | matrix-ultraproduct embedding rigidity | entropy obstruction, no stability | **B** |
| VIII. FK determinant / torsion separator | normalized log determinant | amplification blindness | universal finite-matrix torsion identity + spectral gap | new analytic separator family | **B** |
| IX. Finite-cocycle twisted-factor compiler | projective unitary basis | canonical-trace promotion | realize non-CE factor as finite twisted group factor | finite central extension non-hyperlinear | **B+** |
| X. Channel/Choi hyperlinearity | quantum channels `Ad(U)` | phase and sparse-vector defects | stability/rounding for channel microstates | possible hyperlinear-to-sofic or HNN collapse | **B** |
| XI. Nonlinear Kazhdan rigidity on `PU(d)` | conjugation action on compact projective manifold | linear fixed-space quantifier failure | uniform fixed-point rigidity on inner orbit | direct proof of Route I | **A-** |
| XII. Dimension-free trace-square SOS certificate | `1-|tau([U,V])|^2` | need for operator correction | finite SOS inequality for arithmetic presentation | machine-checkable PRCC certificate | **B+** |

Routes I, III, IV, and V are the recommended breakout portfolio. They attack
four genuinely different failure modes.

---

# Route I -- Projective relative-commutant collapse via full-rank inner superoperators

## 3.1 Construction

Take a proper finitely generated subgroup `C<A` with the exact
finite-dimensional co-density property relevant to Cairn. The concrete
arithmetic prototype is

```text
C=SL_3(Z),   A=SL_3(Z[1/2]).
```

Form the centralizer HNN extension

```text
G=A *_C (C x Z) = <A,t | [t,c]=1 (c in C)>.
```

Choose `a in A-C` and put `w=[t,a]`. Britton normal form gives `w!=e` under
the usual properness hypotheses. Thus in the regular trace `tau_G(w)=0`.

Cairn's existing RCC route tries to show that any hyperlinear microstate
forces `w->1`. We need much less.

## 3.2 The projective target

For `U in U(d)`, write

```text
Ad(U)(X)=UXU*   (X in M_d).
```

This is a unitary on the `d^2`-dimensional Hilbert space `L^2(M_d)`. Scalars
vanish: `Ad(lambda U)=Ad(U)`. Therefore the natural target is not RCC but:

> **PRCC / inner-superoperator transfer.** If `T_n` projectively centralizes
> the microstate image of `C`, then it projectively centralizes the image of
> `A`:
> ```text
> [Ad(T_n),Ad(rho_n(c))] -> 0  (c in C)
> ```
> implies
> ```text
> [Ad(T_n),Ad(rho_n(a))] -> 0  (a in A).
> ```

This is strictly weaker than `[T_n,rho_n(a)]->I`. It only says that
`[T_n,rho_n(a)]` is asymptotically scalar.

## 3.3 The key identity

For any `W in U(d)`, normalized Hilbert--Schmidt norm on `M_(d^2)` gives

```text
||Ad(W)-I||_(2,d^2)^2 = 2-2 |tr_d(W)|^2.             (I.1)
```

Consequently

```text
||[Ad(U),Ad(V)]||_(2,d^2)^2
  = 2-2 |tr_d([U,V])|^2.                             (I.2)
```

This identity is the entire reason the route is interesting. It converts a
trace statement about a group word into a **macroscopic superoperator
distance**.

## 3.4 Conditional proof of non-hyperlinearity

Assume `G` hyperlinear and let `rho_n` be regular-trace matrix microstates.
Put

```text
T_n=rho_n(t), A_n=rho_n(a), C_(n,c)=rho_n(c).
```

The HNN relators imply `||[T_n,C_(n,c)]-I||_2->0`. Hence
`tr([T_n,C_(n,c)])->1`, and by (I.2),

```text
||[Ad T_n,Ad C_(n,c)]||_(2,d_n^2) -> 0.              (I.3)
```

If PRCC holds, then

```text
||[Ad T_n,Ad A_n]||_(2,d_n^2) -> 0.
```

Again by (I.2),

```text
|tr_(d_n)([T_n,A_n])| -> 1.                          (I.4)
```

But `w=[t,a]!=e`, so the regular-character condition of a hyperlinear
microstate requires

```text
tr_(d_n)([T_n,A_n]) -> 0,                            (I.5)
```

a contradiction.

**Conclusion:** PRCC alone proves `G` non-hyperlinear.

No phase needs to be identified. No correction of `T_n` to an exact
commutant is needed. No rank estimate on a `C`-fixed vector is needed.

## 3.5 Why this may be much easier than RCC

Three obstructions are automatically quotiented out.

### Scalar cocycles disappear

The Deligne/projective phenomena that obstruct ordinary HS-stability live in
scalar phases. `Ad` kills them exactly.

### The witness is full rank

Cairn's positive-density adjoint theorem can miss a one-vector outlier in a
`d^2`-dimensional space. Here the object being transported is the unitary
superoperator `Ad(T_n)`, whose normalized `L^2`-mass is always one. The desired
contradiction is `0` versus `sqrt(2)` in superoperator norm, not a disappearing
rank fraction.

### The conclusion is projective

Even a sequence with `[T_n,A_n] approx lambda_n I` is fatal to the regular
trace, because `|tr([T_n,A_n])| approx 1`. Ordinary RCC unnecessarily asks
`lambda_n->1`.

## 3.6 A concrete theorem to prove

For finite generating sets `S_C subset C`, `S_A subset A`, seek constants `K`
and a defect modulus `eta(delta)->0` such that every sufficiently good
approximate representation `rho` of the relevant finite presentation and
every `U in U(d)` satisfy

```text
max_(a in S_A) (1-|tr([U,rho(a)])|^2)
 <= K sum_(c in S_C) (1-|tr([U,rho(c)])|^2)
    + eta(def(rho)).                                  (I.6)
```

The HNN relators kill the right-hand side. Equation (I.6) then kills
hyperlinearity. This is a scalar inequality on traces of words. It is a
materially narrower theorem than flexible HS-stability.

## 3.7 Fast falsification tests

1. **Coset-Bernoulli test.** Cairn already records a Bernoulli firewall for
   full RCC. Check whether its offending `C`-central unitary has `[k,h]`
   genuinely non-scalar. If yes and that crossed product is Connes embeddable,
   PRCC for that pair is false as well.
2. **Finite quotient stress test.** For congruence quotients of `A`,
   numerically minimize the left side of (I.6) subject to projective
   `C`-centrality. Exact co-density predicts zero; near-minimizers reveal the
   likely modulus.
3. **Nonlinear fixed-point test.** Optimize over `PU(d)`, not over arbitrary
   vectors in `L^2(M_d)`. If low-energy projective centralizers appear far
   from the ambient projective commutant, the route dies before any group
   construction work.

## 3.8 Novelty audit

Targeted Cairn searches found ordinary unitary commutant transfer, RCC,
positive-density adjoint no-growth, and centralizer normalization. They did
not surface the projective conclusion (scalar commutator is enough), nor the
trace-square superoperator formulation (I.6).

---

# Route II -- Replace flexible HS-stability by flexible **projective** HS-stability

Route I can be attacked directly, but there is a more conceptual
reformulation.

## 4.1 Channelizing a microstate

Given an approximate unitary representation `rho:F_S->U(d)`, compose with
`Ad`:

```text
bar(rho)(g)=Ad(rho(g)) in PU(d) subset U(d^2).
```

Small normalized-HS multiplication defect for `rho` implies small defect for
`bar(rho)`. Moreover, if `rho` is a regular hyperlinear model then for
`g!=e`,

```text
tr_(d^2)(bar(rho)(g))=|tr_d(rho(g))|^2 -> 0.
```

So regular hyperlinearity survives channelization.

## 4.2 The weaker stability notion

Define a group `A` to be **flexibly projective-HS stable on a class C** if
every approximate representation in that class, after permissible
amplification/compression, is close to an exact homomorphism `A->PU(D)` rather
than to an exact lift in `U(D)`.

This permits scalar 2-cocycles. In particular, the central-extension
obstructions that make ordinary property-(T) HS-stability pathological are no
longer automatically fatal.

For the HNN application one needs even less: projective stability only for the
adjoint microstates that actually arise as `Ad o rho_n`.

## 4.3 Conditional theorem

Let `C<A` be a proper co-dense pair such that every exact finite-dimensional
projective representation appearing as an adjoint lift has

```text
bar(rho)(C)'=bar(rho)(A)'.
```

If the restriction of every regular microstate of the HNN group to `A` is
flexibly projective-HS stable in the above adjoint class, then the HNN group is
non-hyperlinear.

Exactify `Ad rho_n|_A` projectively. The HNN stable letter gives a
superoperator approximately in the commutant of the exactified `C`-image.
Co-density moves it into the commutant of the exactified `A`-image. Transfer
back to the original channel microstate, apply (I.2), and obtain
`|tr(w_n)|->1`, contradicting regular trace zero.

## 4.4 Why this is a serious weakening

The Becker--Lubotzky obstruction says an infinite hyperlinear property-(T)
group cannot have ordinary local HS stability. That obstruction is generated
by honest unitary representations and isolated invariant vectors. It does not
automatically rule out a theorem whose target is **projective** and whose
domain is only the adjoint subclass.

This is the right place to search for a theorem that ordinary stability theory
has not already precluded.

## 4.5 Best candidates

- `SL_n(Z)`, `n>=3`, with a thin profinitely dense subgroup.
- `SL_3(Z)<=SL_3(Z[1/2])`, where finite-dimensional unitary images are rigid
  and projective phases are especially natural.
- Deligne-type central extensions as **test cases**: if projectivization
  really removes the known obstruction, they should become easier rather
  than harder.

## 4.6 Kill condition

If one can build an adjoint approximate representation of the candidate
property-(T) group that stays a fixed projective-HS distance from every exact
`PU`-representation, the route is dead. This is a much sharper counterexample
target than "the group is not HS stable."

---

# Route III -- PI-degree curvature: use polynomial identities to kill the rectangular escape

This route attacks the affine-Leavitt/atlas side rather than RCC.

## 5.1 The exact weakness of the current packet argument

The rectangular countermodel can exchange `M_r tensor M_m` for a
representation in which the "label" factor becomes larger while the
"multiplicity" factor becomes smaller, preserving total normalized trace. A
trace-only argument cannot tell which tensor factor is which.

But **polynomial identity degree can**.

## 5.2 Fixed-degree matrix identity

Let

```text
s_(2r)(X_1,...,X_(2r))
 = sum_(sigma in S_(2r)) sgn(sigma)
   X_(sigma(1))...X_(sigma(2r))
```

be the standard polynomial. Amitsur--Levitzki gives

```text
s_(2r) == 0 on M_r,                                  (III.1)
```

while `s_(2r)` is not an identity on `M_(r+1)`, hence not on `M_(r^2)`.
Crucially, external multiplicity does not matter:

```text
s_(2r)(M_r tensor I_m)=0
```

for every `m`. Thus PI degree is exactly the kind of invariant the
rectangular escape cannot spoof by tensoring spectators.

## 5.3 How to turn this into an HS gap

Choose once and for all an explicit tuple

```text
Y_1,...,Y_(2r) in U(r^2)
```

inside a fixed finite packet algebra such that

```text
kappa_r:=||s_(2r)(Y_1,...,Y_(2r))||_(2,r^2)>0.        (III.2)
```

Suppose a recovered target packet occupies trace fraction `alpha>0` and is
`o(1)`-close to copies of that irreducible `M_(r^2)`-packet. Then

```text
||s_(2r)(Y_1^(n),...,Y_(2r)^(n))||_2
 >= sqrt(alpha) kappa_r-o(1).                         (III.3)
```

On the source side, if the corresponding transported words lie in a
recovered `M_r`-factor, finite-group exactification gives

```text
||s_(2r)(X_1^(n),...,X_(2r)^(n))||_2=o(1).            (III.4)
```

A compressor relation identifying the two evaluations, even only up to
`o(1)`, contradicts (III.3)--(III.4).

## 5.4 Why addition is not a presentation problem

The group need not contain an "addition gate." The standard polynomial is
used by the **proof**, not as a group relator. Each monomial in `s_(2r)` is a
product of finitely many group-word matrices. If the packet relations
determine those matrices, the analyst may form their signed sum externally
and estimate its HS norm.

This is the same reason character projectors and Reynolds averages can be
used in a proof even though they are not group words.

## 5.5 The hard lemma: PI bridge, not same-reservoir rank bookkeeping

The precise new target is:

> **PI bridge lemma.** A fixed collection of transported group words is
> forced by the source packet to lie in a degree-`r` matrix factor, while the
> same words, after one closed transport cycle, are forced by a transverse
> target packet to generate a degree-`r^2` factor on a fixed positive-density
> corner.

This is narrower than proving literal equality of the source and target
reservoirs. It asks only that one fixed polynomial evaluation be transported.

## 5.6 Candidate packet geometry

Finite Heisenberg/extraspecial packets are attractive because a selected
central character has a unique irreducible Stone--von Neumann representation
of prescribed degree. A source Heisenberg packet can expose `M_r`; two
transverse Weyl directions in the target can expose `M_(r^2)`.

A Clifford packet is another option. What matters is:

1. the selected sector has fixed irreducible degree;
2. the sector has a robust finite-group exactification theorem;
3. the target tuple is forced to generate the full factor, not retreat into
   an embedded `M_r` subalgebra.

## 5.7 Why this is different from Cairn's existing Amitsur--Levitzki node

Cairn already has a self-indexing Amitsur--Levitzki **dimension oracle** for
arbitrary finite matrix size and a Schur multiplicity tape. The proposal here
is different: use a **fixed small PI degree** as a basis-free fingerprint
distinguishing the label factor from the multiplicity factor inside the exact
rectangular countermodel. No endogenous readout of the ambient dimension is
required.

## 5.8 Fast falsification test

Instantiate the known rectangular countermodel and search for a forced target
tuple. If every plausible target tuple can be conjugated into an
`M_r tensor I` subfactor, the route fails. If one transverse word is
necessarily outside every such subfactor and makes `s_(2r)` nonzero, the
rectangular escape has been pierced.

---

# Route IV -- Double-centralizer reservoir locking by a finite commuting square

PI curvature fingerprints the label factor. This route instead makes the
multiplicity factor physically observable.

## 6.1 The idea

On a positive-density corner `P C^d`, recover two commuting finite packet
algebras

```text
A ~= M_r tensor I_m,   B ~= I_r tensor M_m,
```

with

```text
A' cap P M_d P = B,   B' cap P M_d P = A.             (IV.1)
```

Now the "multiplicity reservoir" of `A` is not anonymous: it is `B`, generated
by its own finite group words.

A rectangular escape that enlarges `A` must shrink its commutant. But shrinking
the commutant violates the independently enforced `B`-packet.

## 6.2 How to build the two packets

Use two commuting finite groups `H_A,H_B` whose selected irreducible sectors
are full matrix algebras. For example, two extraspecial/Heisenberg packets can
act as left and right Weyl systems. Impose enough cross-commutation to make
them a robust approximate commuting square.

Finite-group HS stability provides dimension-free exactification of each
packet. Corollaries for almost-commuting finite-group homomorphisms can be used
to exactify them jointly after flexible amplification.

## 6.3 The closed-square obstruction

Suppose one compressor relation demands that `A` return as a proper amplified
child `A_1` on the same corner, while preserving `B`. In exact finite
dimensions, mutual commutants force

```text
dim(simple factor of A_1)=dim(simple factor of A)
```

whenever the `B`-factor is unchanged and the generated ambient algebra is
unchanged. A genuine `r |-> r^2` child therefore requires boundary/rank loss.

Close a second compressor in the transverse direction so that any attempted
transfer of loss into `B` is returned to `A`. The result is a
finite-dimensional "commuting-square curvature": the product of the two
factor degrees cannot increase around a closed physical corner.

## 6.4 Conditional contradiction

Assume a common-corner extraction theorem gives exact nearby algebras
`Atilde_n,Btilde_n` satisfying (IV.1) on `P_n`, with
`tr(P_n)>=alpha>0`. Suppose the group relations force the closed cycle

```text
Atilde_n -> Atilde_(n,1) -> ... -> Atilde_n
```

with a strict simple-factor degree multiplication `r |-> q r`, `q>1`, and
preserve the transverse mutual commutant at every leg. Exact
finite-dimensional bicommutant theory says the final degree must equal the
initial degree. Contradiction on a corner of trace `alpha`.

## 6.5 Why this attacks the precise Cairn local minimum

The affine rectangular model wins because "label" and "spectator" are
semantic names, not matrix invariants. Route IV turns the spectator into a
second **word-generated algebra**. The role swap is then observable by
commutants.

This is stronger physical anchoring than another trace ledger and weaker than
tracking literal matrix coordinates.

## 6.6 Hard lemma

The bottleneck is now clean:

> **Approximate mutual-bicommutant extraction.** From two robust finite packets
> that nearly commute and jointly occupy a positive-density spectral corner,
> perturb to two exact finite-dimensional semisimple algebras that are mutual
> commutants on one nearby corner, with dimension-free loss.

This looks closer to finite-group stability and finite-dimensional C*-algebra
perturbation theory than the current open "same reservoir" statement.

## 6.7 Kill test

Build the known exact rectangular escape and add the proposed transverse
packet. If both packets can still be realized by moving to a larger tensor
decomposition, the proposed square is not rigid enough. The right packet pair
is one for which the joint generated algebra is already the full corner.

---

# Route V -- Algebraize a non-CE equivalence relation and obtain a group factor by Pontryagin duality

This route changes the game completely. Instead of forcing a matrix
obstruction from a group presentation, start from a non-CE von Neumann algebra
that is already known to exist and compile it into the canonical group trace.

## 7.1 Existing input

Manzoor's 2025/2026 result gives a non-co-hyperlinear IRS and, as a corollary,
a countable p.m.p. equivalence relation `R` with `L(R)` not Connes embeddable.
Cairn already imports this and then embeds the relation into a property-(T)
relation. The current route stops because a relation factor is not
automatically a discrete group factor.

## 7.2 New compiler theorem

Let `K` be a compact second-countable abelian group with Haar probability and
let a countable group `Lambda` act on `K` by continuous group automorphisms.
Put `A=K-hat`, a countable discrete abelian group. Fourier transform gives

```text
L^infinity(K) ~= L(A),
```

and the algebraic action dualizes to an action of `Lambda` on `A`. Hence

```text
L^infinity(K) rtimes Lambda ~= L(A rtimes Lambda).       (V.1)
```

Therefore:

> **Algebraic-envelope principle.** If a non-CE tracial von Neumann algebra
> embeds trace-preservingly into an algebraic crossed product
> `L^infinity(K) rtimes Lambda`, then `A rtimes Lambda` is non-hyperlinear.

If `A rtimes Lambda` were hyperlinear, its group von Neumann algebra would be
Connes embeddable. Connes embeddability passes to von Neumann subalgebras,
contradicting the embedded non-CE algebra. Equation (V.1) identifies the
ambient crossed product with the canonical group factor.

This is an actual complete compiler theorem. The only open step is
constructing the algebraic envelope.

## 7.3 The high-value target

Strengthen the Chifan--Drimbe--Ioana relation-envelope theorem in one very
specific direction:

> Given the explicit non-CE relation `R`, find a free algebraic action
> `Lambda action K` such that
> ```text
> L(R) embeds into L^infinity(K) rtimes Lambda.          (V.2)
> ```

The action need not have property (T) initially. It only needs to be
algebraic and effectively describable.

## 7.4 Why "free" is useful

For an essentially free action, the group-measure-space algebra is the
relation algebra of its orbit relation, avoiding isotropy bookkeeping. If an
algebraic action envelope is not free, tensor it with an algebraic Bernoulli
shift when that preserves the desired inclusion; products of compact abelian
algebraic actions remain algebraic.

The subtle point is to establish the inclusion at the crossed-product level
before invoking this trick. A non-CE **quotient** of a crossed product is not
sufficient.

## 7.5 Getting a finitely presented group

Suppose `H=A rtimes Lambda` is finitely generated and recursively presented.
Then Higman's embedding theorem places `H` inside a finitely presented group
`Htilde`. Hyperlinearity is inherited by subgroups, so if `H` is
non-hyperlinear then `Htilde` is non-hyperlinear.

Thus the algebraic action compiler only needs to produce a finitely generated
recursively presented semidirect product, not a finite presentation at the
first stage.

## 7.6 Why this is outside the current local minima

- no HS stability;
- no matrix packet recovery;
- no canonical-trace promotion from an arbitrary character;
- no multiplicity return;
- no operator-norm-to-HS conversion.

The canonical trace appears automatically because the final algebra literally
is a group von Neumann algebra.

## 7.7 Fast falsification target

Determine whether the known non-CE relation can be embedded into any orbit
relation of an algebraic action with separable compact abelian base. A
structural obstruction here would kill the route. Conversely, even one
sufficiently explicit algebraic envelope solves the group problem immediately.

---

# Route VI -- Force the non-CE witness to live on a Haar linear subshift

Route V is abstract. Route VI proposes a concrete way to build the required
algebraic action from the same finite-field/LCS machinery already present in
Cairn, but without using it as a robust matrix decoder.

## 8.1 Algebraic process target

Let `Lambda` be finitely generated and let

```text
K <= (F_p^m)^Lambda
```

be a closed shift-invariant subgroup defined by recursively enumerable,
ideally finite-type, linear local constraints. Equip `K` with Haar measure.
The shift action is algebraic.

Its Pontryagin dual is a discrete `F_p[Lambda]`-module `A=K-hat`. If `K` is
generated by finitely many coordinate types, then `A` is finitely generated as
a `Z Lambda`-module, making `A rtimes Lambda` a realistic finitely generated
recursively presented group.

## 8.2 New target statement

Construct such `(Lambda,K)` for which

```text
L^infinity(K) rtimes Lambda
```

is not Connes embeddable. That alone gives a non-hyperlinear group by Route V.

## 8.3 Why LCS/ZPC technology is naturally suited

The current Cairn ZPC route tries to turn a perfect commuting-operator
strategy into a **robust finite-dimensional group relation gap**. That is
precisely where selector freezing and context mismatch become difficult.

A Haar linear subshift route asks for something weaker and more global:

- all constraints are exact in the commuting model;
- the probability measure is Haar by construction;
- local linear constraints become module relations under Pontryagin duality;
- no finite-dimensional soundness theorem is required at the compiler stage.

The non-CE obstruction is carried by the crossed product itself, not by a
finite matrix decoder.

## 8.4 A possible construction pattern

1. Start with a finite LCS/nonlocal-game gadget whose commuting model is
   expressed by affine `F_p`-constraints.
2. Tile copies over a finitely generated shift group `Lambda`.
3. Define `K` as the closed subgroup of all globally consistent labelings.
4. Arrange the game/IRS correlation so that a trace-preserving copy of the
   known non-CE algebra sits in `L^infinity(K) rtimes Lambda`.
5. Dualize to `A rtimes Lambda`.

The hard step is (4), but it is a von Neumann embedding problem rather than an
approximate-representation stability problem.

## 8.5 Why Haar matters

For an arbitrary invariant measure on a symbolic system, the associated
crossed product is not a group factor of the dual module. Haar is what turns
Fourier characters into an orthonormal group basis and makes (V.1) exact.

Thus the decisive design constraint is:

> Make the non-CE process **linear-algebraic enough that its invariant measure
> is Haar**, not merely shift-invariant.

This is a new way to interpret Cairn's finite-field gadgets.

## 8.6 Falsification test

Take the simplest nonlocal-game/IRS witness imported by Cairn and ask whether
its commuting correlation can be realized by a Haar measure on any closed
linear subshift. If basic correlation inequalities already violate the
Fourier positivity identities of Haar algebraic processes, abandon this route
for that witness and search for a game deliberately designed to have
linear-Haar completeness.

---

# Route VII -- Embedding-lock plus Pinsker collision

This route uses the recent asymptotic-freeness/1-bounded-entropy literature,
but with the RAAG firewall built in from the start.

## 9.1 The tempting false theorem

One might hope that if `u_1,u_2` are free Haar unitaries in a matrix
ultraproduct, then no Haar commuting chain

```text
u_1 -- v_1 -- v_2 -- u_2
```

can exist. This is false for arbitrary embeddings: the path RAAG is
hyperlinear and supplies exactly such a configuration in its canonical group
trace.

Therefore the freeness/Pinsker results for ultraproducts of Haar-random
matrices cannot be transferred using moments alone.

## 9.2 What would be enough

Define a pair `(u_1,u_2)` in a tracial algebra to be **Pinsker
embedding-locked** if every trace-preserving embedding of the algebra into a
matrix ultraproduct places the two generators in the class where their
Pinsker algebras are freely independent in the sense of the
Jekel--Kunnawalkam Elayavalli theorem.

Then construct a group `G` containing:

- an embedding-locked free pair `a,b`;
- infinite-order elements `x,y`;
- relations `[a,x]=[x,y]=[y,b]=1`.

If `G` were hyperlinear, the images of `a,b` would have freely independent
Pinsker algebras. Sequential commutation would place `b` in the Pinsker
algebra attached to `a`, while `b` also lies in its own Pinsker algebra. Free
independence forces the intersection to be scalar, contradiction because `b`
is Haar.

## 9.3 Where the real theorem is

The route is therefore not "prove another asymptotic freeness theorem." It is:

> **Build a finitely presented embedding lock** forcing every
> matrix-ultraproduct embedding of a chosen free-product core into the
> generic/random-matrix position covered by existing Pinsker theorems.

Potential wrappers:

- property-(T) subalgebras on both sides that make the embedding orbit
  discrete;
- strongly 1-bounded normalizer envelopes that force a unique Pinsker
  position;
- a rigid amalgam whose embeddings into `R^omega` are unique up to unitary
  conjugacy on the relevant core.

## 9.4 Why this is strategically different

Ordinary stability corrects approximate representations to exact ones.
Embedding-lock rigidity instead classifies **where an exact copy of a tracial
algebra may sit inside a matrix ultraproduct**. This is a model-theoretic/
entropy rigidity problem and may avoid the Becker--Lubotzky barrier entirely.

## 9.5 Literature handle

The relevant tools are not hypothetical:

- Hayes--Jekel--Nelson--Sinclair: 1-bounded entropy absorption in free
  products;
- Houdayer--Ioana: asymptotic freeness of relative commutants and lifting in
  tracial ultraproducts;
- Jekel--Kunnawalkam Elayavalli: Pinsker algebras and upgraded free
  independence for random-unitary ultraproducts.

The missing ingredient is exactly the embedding-lock bridge.

## 9.6 Kill test

Any candidate base algebra must first be tested for two inequivalent
matrix-ultraproduct embeddings, one random/free and one RAAG-like with a
commuting bridge. If both exist, it cannot serve as the lock.

---

# Route VIII -- Fuglede--Kadison determinant / L2-torsion as an amplification-stable separator

Cairn has correctly killed determinant parity and additive index ideas under
tensor amplification. The normalized **log determinant** has different
scaling and deserves a separate audit.

## 10.1 The invariant

For an invertible `D in M_k(M_d)`, define

```text
ell_d(D)=(1/(kd)) log |det D|.
```

Then

```text
ell_(dm)(D tensor I_m)=ell_d(D).                       (VIII.1)
```

So normalized log determinant is exactly amplification-invariant. For an
invertible operator `D` in a finite von Neumann algebra,

```text
log det_FK(D)=tau(log |D|).
```

If `D` has a uniform spectral gap away from zero, this is a continuous
function of the `*`-moments of `D`.

## 10.2 The microstate transfer lemma

Let `P in M_k(C F_S)` be a fixed matrix of noncommutative polynomials. Assume
the regular operator `P(lambda_G(S))` satisfies

```text
P*P >= eta I   (eta>0).                                (VIII.2)
```

If `U^(n)` are hyperlinear microstates for `G`, then moment convergence plus
(VIII.2) gives

```text
ell_(d_n)(P(U^(n))) -> log det_FK(P(lambda_G)),         (VIII.3)
```

after the usual small spectral-cutoff control. Thus any universal
finite-matrix theorem forcing a different limit proves non-hyperlinearity.

## 10.3 What kind of finite-matrix theorem could work

Look for a finite based chain complex over the presentation ring whose
evaluation in **every finite-dimensional unitary model** obeys a
determinant/torsion identity

```text
T_fin=0                                                   (VIII.4)
```

because finite-dimensional determinants are multiplicative and square
matrices have equal left/right determinant, while the regular von Neumann
complex has

```text
T_(2) != 0.                                               (VIII.5)
```

A self-similar HNN or Leavitt-type chain complex is a natural host: its finite
matrix evaluation may have a torsion cancellation that the von Neumann
dimension-scaling picture does not share.

## 10.4 Why this is not the dead determinant-index route

- determinant **phase** is unstable under amplification;
- an additive Fredholm/K-theory index can be diluted;
- normalized log determinant is multiplicative and amplification-invariant by
  (VIII.1).

The price is spectral control: near-zero singular values make `log` singular.
That is why (VIII.2) or a regularized determinant must be built into the
construction.

## 10.5 Important honesty condition

With a fixed spectral gap, log determinant is ultimately a continuous tracial
functional. Therefore this route does **not** magically bypass the need for a
finite-matrix-only theorem. Its value is that determinant multiplicativity and
torsion give a new source of such theorems that ordinary trace polynomials may
conceal.

## 10.6 Fast falsification test

Evaluate candidate torsion complexes on Cairn's exact rectangular
countermodel. If the normalized log determinant agrees on the source and
escaped target, the invariant is blind to the local minimum and should be
dropped. If a fixed gap survives and the values differ, this route becomes
very high priority.

---

# Route IX -- Compile a non-CE algebra into a finite-cocycle twisted group factor

This is a second global route around canonical-trace promotion.

## 11.1 The compiler lemma

Let `Gamma` be a countable group and

```text
omega:Gamma x Gamma -> mu_m
```

a finite-valued scalar 2-cocycle. Suppose the twisted group von Neumann
algebra `L_omega(Gamma)` is not Connes embeddable.

Form the central extension

```text
1 -> mu_m -> Gammatilde -> Gamma -> 1
```

with multiplication encoded by `omega`. The central character projection
`p_chi in L(Gammatilde)` has a corner

```text
p_chi L(Gammatilde) p_chi ~= L_omega(Gamma).            (IX.1)
```

If `L(Gammatilde)` were Connes embeddable, every corner would be. Hence
`Gammatilde` is non-hyperlinear. This proof is complete.

## 11.2 New target

Instead of forcing a non-CE BCS algebra into a pre-existing signed corner,
reverse the construction:

> Build a known non-CE factor with a countable orthonormal unitary basis
> `{u_g}_(g in Gamma)` satisfying
> ```text
> u_g u_h=omega(g,h)u_(gh),   omega(g,h) in mu_m.        (IX.2)
> ```

Then the factor is a finite-cocycle twisted group factor and (IX.1) produces
a non-hyperlinear group.

This is a "unitary error basis" / projective-group-basis formulation of the
groupification problem.

## 11.3 Why it may be easier than direct groupification

A commuting-operator/nonlocal-game construction naturally produces Pauli and
Clifford algebras, which already possess orthonormal projective unitary bases
with finite phases. The open problem is to retain that projective basis
through the non-CE construction, rather than to prove a robust HS soundness
theorem for an arbitrary group presentation.

The phase is not a nuisance here: finite phase is exactly what the central
extension absorbs.

## 11.4 Relation to existing Cairn work

This is adjacent to signed-corner and phase-safe LCS ideas but changes the
direction of attack. Existing branches install a non-CE algebra into a
specially engineered group corner and then struggle with trace uniqueness/
robust soundness. Route IX asks for a structural property of the **non-CE
factor itself** and then applies a formal central-extension compiler.

## 11.5 Kill test

Inspect the concrete non-CE game factor/GNS algebra used by the imported
separation. If every natural Pauli-word basis collapses under the quotient or
fails orthogonality in the target trace, the finite-cocycle basis requirement
is too strong for that witness.

---

# Route X -- Treat hyperlinear microstates as quantum channels, not matrices

This is the broad version of Routes I--II.

## 12.1 Canonical channel lift

Every unitary microstate produces an inner quantum channel

```text
Phi_g=Ad(U_g).
```

The normalized superoperator trace is

```text
Tr_norm(Phi_g)=|tr(U_g)|^2.                            (X.1)
```

Thus a regular unitary microstate becomes a regular **channel** microstate.
The channel representation forgets phases but preserves multiplication
exactly at the projective level.

## 12.2 New global question

Instead of asking whether a property-(T) group is HS stable in matrices, ask:

> Are its **inner-channel microstates** stable among trace-preserving quantum
> channels or projective unitary channels?

This domain is much smaller than all maps to `U(d)`, and the target can be
larger than exact inner channels during an intermediate correction step.

A Stinespring dilation may convert approximate channel multiplicativity into
an exact finite-dimensional representation on a slightly larger space without
choosing phases coherently.

## 12.3 Possible two-step correction

1. Correct `{Phi_g}` as completely positive trace-preserving maps using
   spectral gap / property (T) in the convex channel space.
2. Prove that a corrected channel sufficiently close to an inner automorphism
   is near an exact inner/projective automorphism.

The first step lives in a convex set, unlike unitary stability. Convexity may
permit averaging procedures that are impossible in `U(d)`.

## 12.4 HNN payoff

For a stable letter `T`, only the channel `Ad(T)` needs to land in the ambient
commutant. This is exactly Route I. A successful general channel-stability
theorem would therefore simultaneously solve multiple RCC-style branches.

## 12.5 Hyperlinear-to-sofic variant

If a regular channel microstate can be rounded to a finite stochastic
automorphism table, one may recover a permutation model without ever choosing
matrix phases. This is a different intermediate category from Cairn's current
direct Markovization: the input is the **conjugation channel table**, which
already has nonnegative Choi matrices and phase quotient built in.

The challenge is to extract a common classical latent algebra; the advantage
is that positivity is native rather than introduced by dephasing.

## 12.6 Kill test

Find a hyperlinear property-(T) group with an adjoint/channel microstate
sequence demonstrably far from every exact projective channel representation.
Such a sequence would show that projectivization does not remove the stability
obstruction.

---

# Route XI -- Nonlinear Kazhdan rigidity on the projective unitary manifold

This is a concrete strategy for proving Route I without full projective
representation stability.

## 13.1 Why linear spectral gap has the wrong quantifier

Cairn's RCC audit correctly observes that property (T) cannot say that the
`C`-fixed vector space equals the `A`-fixed vector space. An exact `C`-fixed
vector is legal.

But the HNN stable letter is not an arbitrary vector in that fixed space. It
lies on the nonlinear compact submanifold

```text
I_d={Ad(U):U in U(d)} subset U(d^2).
```

The extra algebraic constraints defining `I_d` are enormous.

## 13.2 New fixed-point theorem to seek

Let `C<A` be the arithmetic co-dense pair. Let `rho` be an approximate
representation of `A`. Consider the conjugation action of `C` on `PU(d)`:

```text
c . [U]=[rho(c) U rho(c)*].
```

Seek a dimension-free theorem of the form:

> If `[U] in PU(d)` is `epsilon`-fixed by a Kazhdan generating set of `C`,
> then it is `f(epsilon+def(rho))`-fixed by the ambient generator `h`,
> provided every exact finite-dimensional model has `C`- and `A`-fixed
> projective sets equal.

This is a nonlinear fixed-point stability theorem on `PU(d)`, not a statement
about all vectors in a Hilbert representation.

## 13.3 Why exact co-density becomes stronger on the inner orbit

For an exact finite-image representation, projective centralizers are compact
algebraic subgroups of `PU(d)`. If the image of `C` equals the image of `A`,
those fixed sets are literally equal. The question is whether this equality
has a uniform Lojasiewicz/Kazhdan modulus on the restricted algebraic variety
of inner automorphisms.

This is reminiscent of quantitative algebraic geometry rather than ordinary
group stability.

## 13.4 Local/far split

Cairn's Iwahori program already closes a near sector by Newton-style analysis
and fails in the far sector. The projective manifold suggests a cleaner split:

- **near fixed set:** use a uniform Hessian/Kazhdan estimate on `PU(d)`;
- **far sector:** use compactness plus a finite packet/character argument to
  show a definite projective energy floor.

Because the energy is the trace-square quantity
`1-|tau([U,c])|^2`, phases cannot create false far-sector minima.

## 13.5 Computational experiment

For small congruence quotients of `SL_3`, optimize

```text
E_C(U)=sum_(c in S_C)(1-|tr([U,rho(c)])|^2)
```

against

```text
E_h(U)=1-|tr([U,rho(h)])|^2.
```

If the ratio `E_h/E_C` remains bounded across irreducible packets and direct
sums, that is evidence for (I.6). If it blows up with quotient size, this
implementation is unlikely to work.

---

# Route XII -- Search for a dimension-free trace-square SOS certificate

Route XI is analytic. Route XII makes the same target algebraic and
potentially machine-verifiable.

## 14.1 Polynomial form of the energy

For unitary word values, the quantity

```text
1-|tr([U,V])|^2
```

is a degree-four trace polynomial in the matrix entries and their conjugates.
It is also exactly half the squared normalized-HS distance between the
corresponding inner superoperators.

Thus PRCC can be phrased as a noncommutative trace-polynomial inequality.

## 14.2 Certificate target

For a finite presentation of the arithmetic pair, search for a rational
sum-of-squares / positive-semidefinite trace identity of the schematic form

```text
1-|tau([u,h])|^2
 <= K sum_(c in S_C)(1-|tau([u,c])|^2)
    + sum_j tau(R_j* R_j)
    + presentation defect terms,                     (XII.1)
```

where `R_j` vanish in exact representations of the defining relations. A
certificate with `K` independent of matrix size proves the desired
projective transfer for every matrix model at once.

## 14.3 Why trace-square is better than raw trace

The modulus square is phase-invariant and positive. It can be represented as
the character of the adjoint representation. This moves the problem into a
positivity cone where semidefinite methods and property-(T) sum-of-squares
certificates are naturally available.

## 14.4 How to search without falling into the fixed-degree trace-separator trap

Do not ask an SDP to discover the entire non-hyperlinearity proof. Fix the
desired inequality (XII.1) and use the arithmetic presentation to search only
for the missing positive certificate. The candidate is falsifiable by finite
quotients, so numerical work can prune it quickly.

## 14.5 Payoff

A successful certificate would be stronger than a numerical observation and
weaker than full HS stability. It would prove exactly the scalar commutator
collapse needed by Route I and could plausibly be imported into a formal proof
environment.

---

# 15. Three hybrid attacks that combine the strongest ideas

## Hybrid A -- PRCC + finite packet positive-density wall

The only possible failure of a direct projective transfer may occur on a
low-density exceptional packet. Use Cairn's existing finite Schur/Heisenberg
packet machinery not to recover the whole representation, but only to prove:

```text
E_h(U)>=epsilon
 ==> a fixed packet carries at least alpha(epsilon) of E_h.
```

Then use finite-group exactification on that packet and exact co-density to
force its projective energy to zero. This converts the existing
positive-density technology into a proof about a **full-rank inner
automorphism** rather than a sparse commutant vector.

This is likely the most compatible way to reuse Cairn's mature packet library
without re-entering the same reservoir maze.

## Hybrid B -- PI curvature + double-centralizer lock

Use Route IV to identify the physical source/multiplicity decomposition and
Route III only as the final one-number detector. The second packet prevents
the target tuple from retreating to an embedded `M_r`, while `s_(2r)` gives a
fixed HS contradiction once the full `M_(r^2)` target is exposed.

This substantially lowers the burden on either theorem individually:

- the bicommutant theorem need only pin one transverse generator;
- the PI theorem need only detect one fixed tuple.

## Hybrid C -- Algebraic action + finite-cocycle compiler

Route V asks for an untwisted algebraic crossed product. Route IX allows a
finite scalar cocycle. Therefore the true global target can be relaxed to

```text
N embeds into L_omega(A rtimes Lambda),
omega in Z^2(A rtimes Lambda,mu_m).
```

A finite central extension then untwists the ambient algebra into a corner of
an ordinary group factor. This may be much more natural for Pauli/LCS
constructions, where finite phases are unavoidable but completely controlled.

---

# 16. What not to claim yet

These routes are designed as breakthrough research directions, not as a
declaration that the non-hyperlinear group problem has been solved.

The complete implications in this memo are:

1. **PRCC implies the explicit HNN group is non-hyperlinear.** The proof is in
   Section 3.4.
2. **An embedding of a non-CE algebra into an algebraic compact-abelian
   crossed product produces a non-hyperlinear semidirect-product group.** The
   proof is in Section 7.2.
3. **A non-CE finite-cocycle twisted group factor produces a non-hyperlinear
   finite central extension.** The proof is in Section 11.1.
4. **A uniform finite-matrix determinant/torsion separator with a regular
   spectral gap produces non-hyperlinearity.** The transfer is in Section
   10.2.

The genuinely open parts are the boxed compiler/rigidity statements in each
route.

---

# 17. Recommended order of attack

## First: PRCC, not RCC

Replace the current HNN target everywhere by the projective trace-square
target

```text
|tau([t,a])| -> 1.
```

The first concrete object to study is the energy pair

```text
E_C(U)=sum_(c in S_C)(1-|tau([U,c])|^2),
E_h(U)=1-|tau([U,h])|^2.
```

This is the smallest theorem that would already solve the group problem
through the existing co-dense HNN construction.

## Second: attack the exact rectangular countermodel with a PI test

Do not add another trace recurrence. Instantiate `s_(2r)` or a small central
polynomial on the explicit source/target packet words and ask whether any
forced target tuple has a nonzero value in the rectangular model. This
experiment has a binary outcome and directly tests whether PI degree sees what
trace does not.

## Third: build a transverse multiplicity packet

Try to expose the multiplicity factor as a second finite group algebra and
prove approximate mutual-bicommutant extraction. If this works, the
same-reservoir problem becomes a finite-dimensional perturbation theorem
rather than a semantic alignment problem.

## Fourth: start an independent global algebraic-action program

Search the imported non-CE relation/game constructions for an algebraic
process hidden in the proof. In particular, identify whether the relevant
p.m.p. systems can be replaced by Haar measures on finite-field linear
subshifts. This line is almost orthogonal to the current matrix-decoder graph
and is therefore valuable diversification.

## Fifth: only then revisit entropy/Pinsker

Do not use free-moment arguments without an embedding-lock theorem. The path
RAAG is the mandatory counterexample check for every proposed ultraproduct
commuting-chain obstruction.

---

# 18. Minimal "breakthrough theorem" statements to put on the wall

The following four statements are narrow enough that proving **any one** would
radically change the program.

### BT-1 -- Projective commutant transfer

For a concrete co-dense arithmetic pair `C<A`, regular approximate
representations satisfy

```text
max_(a in S_A)(1-|tau([U,a])|^2) <= K E_C(U)+o(1)
```

uniformly in matrix dimension.

**Consequence:** explicit non-hyperlinear HNN group.

### BT-2 -- PI bridge

A fixed source packet evaluation of `s_(2r)` is `o(1)`, while its closed-cycle
target evaluation has HS norm at least `kappa>0` on a fixed trace fraction.

**Consequence:** closes a rectangular-escape branch without multiplicity
counting.

### BT-3 -- Common-corner mutual-bicommutant extraction

Two approximately commuting robust finite packets on a positive-density
carrier perturb, with dimension-free loss, to exact mutual commutants on one
nearby carrier.

**Consequence:** physical reservoir pinning; combines with existing compressor
cycles.

### BT-4 -- Algebraic non-CE envelope

The explicit non-CE relation algebra embeds trace-preservingly into

```text
L^infinity(K) rtimes Lambda
```

for one effectively presented compact abelian algebraic action.

**Consequence:** `K-hat rtimes Lambda` is non-hyperlinear; Higman gives a
finitely presented overgroup when needed.

---

# 19. Novelty checks against the supplied Cairn graph

Targeted searches in the supplied snapshot found nearby but distinct nodes:

- ordinary RCC / unitary commutant transfer;
- property-(T) positive-density adjoint no-growth;
- flexible HS-stability and weak ucp-stability conditional routes;
- the Amitsur--Levitzki self-indexing dimension oracle;
- Schur residual multiplicity tapes;
- rectangular Wedderburn and same-reservoir open claims;
- character-rigid signed corners;
- non-cohyperlinear IRS and the property-(T) relation envelope;
- character Diracization;
- Markovization/coherent-configuration hyperlinear-to-sofic routes.

The following exact directions did **not** surface as existing Cairn
claims/routes in the targeted audit:

1. replacing RCC by **projective** RCC because scalar commutators already
   contradict the regular trace;
2. using the exact identity
   `||Ad(W)-I||_2^2=2-2|tau(W)|^2` as the principal obstruction;
3. fixed-small-degree PI identities as a **label-factor fingerprint** for the
   existing rectangular countermodel;
4. physically exposing the multiplicity factor as a second robust packet and
   locking the pair by mutual commutants;
5. compiling a non-CE relation into a group factor through a **compact abelian
   algebraic action** and Pontryagin duality;
6. asking the non-CE witness itself to be a Haar **linear subshift** process;
7. a finite-cocycle twisted-factor compiler as a reverse direction from
   non-CE factor to group;
8. normalized FK log-determinant / torsion as an amplification-invariant
   finite-matrix separator;
9. the explicit RAAG-firewalled "embedding-lock" formulation of Pinsker
   obstruction.

That is the sense in which this memo uses "new": not merely a renamed Cairn
frontier node, and not another local optimization inside the currently
dominant atlas/Iwahori/Fanizza recurrences.

---

# 20. External tools that materially support these routes

This is not a literature survey, but the following results are directly
relevant to the proposed new targets:

- **Gowers--Hatami**, *Inverse and stability theorems for approximate
  representations of finite groups*, arXiv:1510.04085 -- robust finite-group
  exactification in Schatten/HS settings.
- **Becker--Lubotzky**, *Group stability and Property (T)*,
  arXiv:1809.00632 -- explains why ordinary HS stability of infinite
  hyperlinear property-(T) groups is the wrong target.
- **Dogon**, *Flexible Hilbert-Schmidt stability versus hyperlinearity for
  property (T) groups*, arXiv:2211.10492 -- conditional central-extension
  route and weak-ucp perspective.
- **Hayes--Jekel--Nelson--Sinclair**, *A random matrix approach to absorption
  in free products*, arXiv:1912.11569 -- 1-bounded entropy absorption
  machinery.
- **Houdayer--Ioana**, *Asymptotic freeness in tracial ultraproducts*,
  arXiv:2309.15029 -- relative-commutant asymptotic freeness and lifting
  technology.
- **Jekel--Kunnawalkam Elayavalli**, *Upgraded free independence phenomena for
  random unitaries*, arXiv:2404.17114 -- Pinsker algebras and sequential
  commutation in the random-unitary ultraproduct setting.
- **Manzoor**, *There Is An Equivalence Relation Whose von Neumann Algebra Is
  Not Connes Embeddable*, arXiv:2502.06697v2 -- non-cohyperlinear IRS and
  non-CE equivalence relation.
- **Chifan--Drimbe--Ioana**, *Embedding universality for II_1 factors with
  property (T)*, arXiv:2205.07442 -- universal relation/factor envelopes using
  wreath-like constructions.

The Pinsker papers are intentionally used only with the embedding-lock caveat;
the path-RAAG counterexample prevents a model-independent extrapolation.

---

# 21. Final strategic recommendation

The Cairn graph is currently rich enough that adding another local
carrier-return lemma is unlikely to change the shape of the problem. The most
valuable move is to **weaken the conclusion before strengthening the proof**.

For the HNN branch, replace

```text
[t,a] -> 1
```

by

```text
[t,a] -> a scalar,
```

then quotient phases with `Ad`. This creates a full-rank normalized-HS witness
whose distance is exactly controlled by the modulus square of the group trace.
It attacks the stability bottleneck at a genuinely weaker level and uses the
regular character itself as the amplifier.

For the packet branch, stop asking trace to identify a tensor factor. Trace
cannot. Use either a **PI-degree fingerprint** or a **second mutual-commutant
packet** to make the tensor factor an algebraic invariant.

And in parallel, pursue a route that does not touch HS stability at all: turn
the already available non-CE relation into an **algebraic compact-action
crossed product**, where Pontryagin duality automatically supplies a canonical
group trace.

Those three moves -- **projectivize, fingerprint matrix degree, algebraize the
relation** -- are the cleanest ways to break out of the present Cairn local
minima.

---

## Current-repository integration notes

The memo above is preserved as the source proposal. Against the current graph,
the following deduplication applies:

- Route I is wired as `projective-trace-square-transfer-for-sl3-pair` and its
  goal route. It is strictly weaker than
  `relative-commutant-collapse-for-sl2-pair` and
  `no-spherical-leak-in-matrix-ultraproducts`, but stronger than merely
  excluding the one exact quasi-regular HNN profile.
- Route III is wired as `fixed-pi-degree-fingerprints-packet-label-factor`.
  It is distinct from the unbounded self-indexing oracle
  `two-generator-amitsur-levitzki-dimension-oracle` and from
  `multiplicity-pi-turing-tape`.
- Route IV is wired as `common-corner-mutual-bicommutant-extraction`. The
  existing `full-packet-bicommutant-synchronization` is a one-packet
  commutant-to-carrier target; this new target exactifies two transverse
  packets as mutual commutants.
- Routes V--VI are wired through
  `algebraic-compact-action-envelope-for-non-ce-relation` and the established
  Pontryagin compiler implication.
- Route IX's compiler implication is already subsumed by
  `thom-central-corner-criterion`. The reverse search now has an exact
  firewall: `projective-basis-character-criterion` characterizes when a GNS
  factor natively has such a basis, and
  `twisted-group-basis-forces-affine-context-support` proves that native basis
  involutions occupy one uniform affine slice in every Boolean context. Thus a
  nonlinear BCS model of this form has already factored through an LCS/affine
  refinement; Fourier-sum observables return to the existing additive-corner
  groupification interface. No duplicate finite-cocycle compiler is added.
- Route VIII is **refuted as stated**. A gap for the regular operator does not
  transfer unregularized log determinants through microstates. The exact
  free-group counterexample is
  `free-group-laplacian-refutes-regular-gap-fk-transfer`, the corrected limit
  theorem is `fk-transfer-needs-uniform-log-integrability`, and
  `sublinear-block-poisons-normalized-torsion` records the general `o(d)`-corner
  contamination firewall. Only a separator with a common spectral floor on
  every approximate finite evaluation survives, and at that strength it is a
  generic robust finite-matrix separator rather than a determinant shortcut.
- Routes VII, X--XII remain portfolio attack notes. They are not promoted
  to separate graph claims until they produce a concrete host/certificate;
  this avoids duplicating the existing entropy, channel, and arithmetic-RCC
  frontiers.

The machine lane also admits a useful strengthening independent of all four
portfolio routes. `threshold-free-reverse-kleene-higman-diagonal` shows that a
reverse-Kleene program may enumerate only a formal triviality proof: it never
needs to read a decoder threshold or modulus. Qualitative NONHALT membership
of the mark in the hyperlinear radical suffices, even for a uniformly
recursively enumerable presentation, after which effective Higman embedding
gives a finitely presented non-hyperlinear overgroup. The compactness
equivalence is `hyperlinear-radical-presentation-compactness`; the tensor-power
limit on unconditioned collapse is
`reverse-kleene-unconditioned-collapse-forces-fd-invisibility`.

The machine lane has since weakened again. For the actual hyperlinearity
contradiction it is enough that a rational group-algebra mark collapse along
canonical-delta microstates, by `canonical-profile-kleene-higman`; arbitrary
noncanonical ultraproduct homomorphisms need not kill it. This gives the
minimal current Fanizza target `fanizza-canonical-profile-groupification`.
For word marks, tensor powers also sharpen the unconditional compactness
statement to `hyperlinear-radical-is-finitely-witnessed`: a radical word in an
r.e. presentation already lies in the radical of one finite relator prefix.
The profile-relative analogue is
`canonical-profile-word-collapse-one-window`, where the finite trace side
conditions cannot be dropped.

Two later repository corrections also constrain the portfolio. Bass--Serre
marginal matching alone cannot charge rank-one forbidden mass, and the native
Fanizza C18 guard does not globally reduce to three bits: its Pauli phase turns
off at the terminal cell. Consequently none of Routes III--IV may rely on a
finite graph-of-finite-groups payment or on the refuted global Pauli identity;
they must use genuine compressor/holonomy geometry and the surviving native
one-triangle incidence.

There is also a representation-theoretic firewall on Route IV that is not
visible in its first formulation: a second **fixed finite** packet cannot
generate the full unbounded multiplicity algebra `M_m`, because its irreducible
degrees are bounded and repeated types leave a spectator commutant.  The graph
therefore records the honest strengthened target: a fixed label packet plus a
**scalable word-generated reservoir algebra**, or a separate theorem killing
the residual spectator.  Finite-group exactification alone cannot establish
the advertised mutual-bicommutant identity.
