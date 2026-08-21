# Normal generation in the Fournier-Facio quotient

**Current status (superseding the 2026-08-17 quarantine).** The Hull--Osin
routing argument below was subsequently checked against the source papers and
independently audited; the final record is §9 and
`notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md`.  Cairn therefore
uses it as a paper-level established input in
`defect-normally-generates-torsion-free-quotient`.  It is still **not Lean
formalized**: acylindrical hyperbolicity and small cancellation remain outside
the kernel-checked boundary.  Everything downstream of the routing data is
formalized.  The older prohibition was an audit-stage status, not the current
mathematical verdict, and is retained only in repository history rather than as
a contradictory live banner.

**What is proved here.** The Fournier-Facio construction of a finitely
presented torsion-free non-sofic group can be run so that the *whole group*
is the normal closure of the image of its simple factor.  Concretely:

> **Theorem 1.** There is a finitely presented torsion-free group `G` with
> property (T), a surjection `pi : E -> G` from the Fournier-Facio double HNN
> extension `E`, and a finitely presented infinite simple torsion-free group
> `S <= E`, such that `pi|_S` is injective and
>
>     G = <<pi(S)>>^G .

Combined with the machine-checked obstruction
(`normal-kazhdan-defect-non-mf`), Theorem 1 yields:

> **Theorem 2.** `G` is a finitely presented torsion-free group that is not
> MF in the norm-matrix-corona sense.  Indeed *every* homomorphism from `G`
> to the unitary group of a norm matrix corona is trivial.

The only new mathematics is a one-line strengthening of Hull's common
quotient corollary, isolated below as Theorem B; its proof is Hull's own
proof of [Hul16, Corollary 7.4] with a single substitution, licensed by a
published lemma of Osin.

Everything cited is quoted verbatim from the source papers in §6.

---

## 1. The published construction

Fournier-Facio, *A torsion-free non-sofic group*, arXiv:2608.02025v1
(3 August 2026), §2.  Ingredients, all chosen torsion-free:

* `U` — a universal finitely presented torsion-free group (Higman;
  Belegradek--Szczepanski; Chiodo): it contains a copy of every finitely
  presented torsion-free group.
* `S` — a finitely presented **infinite simple** torsion-free group
  (Burger--Mozes, or Hyde--Lodha).
* `H` — a torsion-free hyperbolic group with property (T) (a random group at
  suitable density, Zuk).  It is finitely presented, non-elementary, and
  `K(H) = {1}`.

Steps:

1. `U` embeds in a finitely presented torsion-free property-(T) group `P`,
   by small cancellation over the relatively hyperbolic pair `(U * H, U)`:
   add relations identifying each generator of `U` with an element of `H`.
   Torsion-freeness is preserved by [Osi10, Theorem 2.4(5)] (§6.3), and `P`
   is a quotient of `H`, hence has (T).
2. By universality of `U`, `P` contains a subgroup `P_1 x P_2 x S` with
   `P_i ~= P`.  Let `E` be the double HNN extension of `P` with stable
   letters `u_1, u_2`, where `u_i P u_i^{-1} = P_i`.  Then `E` is torsion-free,
   finitely presented (the edge groups are finitely generated), and
   acylindrically hyperbolic: the Bass--Serre tree has a path of length 2
   with trivial stabiliser because `P_1` and `P_2` are disjoint edge groups,
   so [MO15] applies.
3. A common quotient `pi : E ->> G` of `E` and `H` is produced by
   [Hul16, Corollary 7.4], injective on a prescribed finite set; `G` is
   torsion-free by [Hul16, Theorem 7.1(e)] (§6.2), finitely presented
   because only finitely many relators are added, and has (T) because it is
   a quotient of `H`.  Choosing the prescribed finite set to contain some
   `s in S \ {1}` forces `pi(S) != 1`, hence `pi|_S` injective by simplicity
   of `S`.

Write `Gamma = pi(P)`, `t_i = pi(u_i)`.  Then `Gamma` has (T) (quotient of
`P`), is infinite (it contains `pi(S) ~= S`), `G = <Gamma, t_1, t_2>` and
`t_i Gamma t_i^{-1} <= Gamma`.

**A convention note** *(corrected 2026-08-15; the earlier version of this
paragraph wrongly claimed the paper had the other conjugate)*.  The paper
itself defines

    J := t_1^{-1} pi(S) t_1

(arXiv:2608.02025v1, §2, checked against the PDF on 2026-08-15), which is
exactly the subgroup satisfying the hypotheses of its Proposition 1.2:
`[P_1, S] = 1` gives `[t_1 Gamma t_1^{-1}, pi(S)] = 1`, i.e.
`[Gamma, t_1^{-1} pi(S) t_1] = 1`, and `t_1 J t_1^{-1} = pi(S) <= Gamma`.
The paper's own reduction of `Gamma cap J = 1` to
`pi(P_1) cap pi(S) = 1` matches this convention.  Nothing below depends on
which of the two conjugates is used; only that `J` is a conjugate of `pi(S)`
centralising `Gamma` with `t_1 J t_1^{-1} <= Gamma`.

## 2. What the analytic theorem demands, and what the defect is

The repository's machine-checked theorem
(`GroupApproximation/Sofic/NormalKazhdanMFRadical.lean`,
`KazhdanCompressionCore.normalKazhdan_le_normMFResidual`, and the
`¬ IsWeakMF` endpoint in `NormalKazhdanCompressionObstruction.lean`) takes:

* `C : KazhdanCompressionCore Gamma E` — a homomorphism `iota : Gamma -> E`
  with `Gamma` Kazhdan, an element `t` with `t iota(Gamma) t^{-1} <= iota(Gamma)`,
  and an element `c` centralising `iota(Gamma)`;
* a **normal, nontrivial, property-(T)** subgroup `K <= C.defectNormal`,

where `C.defectNormal = <<{ [t c t^{-1}, iota(gamma)] : gamma in Gamma }>>^E`,
and concludes that every homomorphism of `E` into the unitary group of a norm
matrix corona kills `K` pointwise; in particular `E` is not MF.

Instantiate with `iota` the inclusion of `Gamma = pi(P)`, `t = t_1`, and
`c in J \ {1}`.  Then `d := t_1 c t_1^{-1} in pi(S) \ {1}`.

**Lemma 0.**  `C.defectNormal = <<pi(S)>>^G`.

*Proof.*  `(<=)` Each generator `[d, gamma] = d (gamma d^{-1} gamma^{-1})` is a
product of two conjugates of `d^{\pm 1} in pi(S)`, so lies in `<<pi(S)>>^G`,
which is normal; hence the normal closure of the generators is contained in
it.

`(>=)`  `C.defectNormal` is normal in `G`, so
`C.defectNormal cap pi(S)` is normal in `pi(S)`.  Since `S` is infinite
simple it is non-abelian and centreless, so `pi(S)` is non-abelian simple and
`d != 1` is not central in `pi(S)`: there is `gamma in pi(S) <= Gamma` with
`[d, gamma] != 1`.  That element lies in `C.defectNormal cap pi(S)`, which is
therefore not trivial, hence equals `pi(S)` by simplicity.  So
`pi(S) <= C.defectNormal` and therefore `<<pi(S)>>^G <= C.defectNormal`. ∎

So the *entire* remaining question is whether `<<pi(S)>>^G` has property (T),
and the cheapest sufficient form is `<<pi(S)>>^G = G`, because `G` has (T).
That is exactly Theorem 1.

## 3. Why the demand is not free

`E` itself is **never** normally generated by `S`:

    E / <<P>>^E = <u_1, u_2 | > = F_2 ,

and `<<S>>^E <= <<P>>^E`, so `E / <<S>>^E` surjects onto a free group of rank
2.  Hence no choice of ingredients makes `pi` inherit normal generation from
`E`; the normal generation must be *created* by the small-cancellation step,
and it cannot be created by relators lying inside `E` alone (adding such a
relator is an uncontrolled quotient of `E`, outside the small-cancellation
regime).  This is why the work below happens inside Hull's argument.

## 4. The tool

Throughout, `AH` is the class of acylindrically hyperbolic groups, `K(G)` the
finite radical (maximal finite normal subgroup), and *suitable with respect
to `A`* is Hull's Definition 1.4 (§6.1): `Gamma(G, A)` is hyperbolic with `G`
acting acylindrically, the subgroup acts non-elementarily, and the subgroup
normalises no nontrivial finite subgroup of `G`.

**Lemma A.**  Let `G in AH` be torsion-free and let `D` be an infinite normal
subgroup of `G`.  Then `D` is a suitable subgroup of `G`, with respect to any
generating set `A` for which `Gamma(G, A)` is hyperbolic and the `G`-action on
it is acylindrical and non-elementary.

*Proof.*  Such an `A` exists by [Hul16, Theorem 3.12(4)] (§6.4).  A normal
subgroup satisfies `D^g = D` for all `g`, so `|D^g cap D| = |D| = infinity`:
`D` is *s-normal* in `G` in the sense of [Osi16].  By [Osi16, Lemma 7.1]
(§6.5), every s-normal subgroup of a group acting acylindrically and
non-elementarily on a hyperbolic space acts non-elementarily.  This gives
conditions 1 and 2 of Definition 1.4.  Condition 3 is vacuous: `G` is
torsion-free, so its only finite subgroup is trivial (equivalently
`K_G(D) = {1}`, which by [Hul16, Lemma 5.5] is the criterion for
suitability). ∎

**Theorem B (common quotient onto a prescribed normal subgroup).**  Let
`G_1, G_2 in AH` be finitely generated with `K(G_i) = {1}`, let `D` be an
infinite normal subgroup of `G_2`, and let `F_i subset G_i` be finite
subsets.  Then there exist a group `Q in AH_0` and surjective homomorphisms
`alpha_i : G_i ->> Q` such that

  (i) `alpha_i|_{F_i}` is injective for `i = 1, 2`;
 (ii) `alpha_2(D) = Q`;
(iii) every element of `Q` of finite order `n` is the image of an element of
      order `n` of `G_1 * G_2`; in particular `Q` is torsion-free if `G_1`
      and `G_2` are;
 (iv) `Q` is finitely presented if `G_1` and `G_2` are.

*Proof.*  This is Hull's proof of [Hul16, Corollary 7.4] (quoted in full in
§6.2) with one substitution.  Let `F = G_1 * G_2`, so `{G_1, G_2} ,->_h F`.

Hull chooses infinite order `f_1, f_2 in G_1` with `{<f_1>, <f_2>} ,->_h G_1`
and infinite order `h_1, h_2 in G_2` with `{<h_1>, <h_2>} ,->_h G_2`, both by
[Hul16, Corollary 5.7] applied to `G_1` and to `G_2` (legitimate because
`K(G_i) = {1}` makes `G_i` suitable in itself), and sets
`S_{suit} = <h_1, h_2>`.

**The substitution: apply Corollary 5.7 to `D` instead of to `G_2`.**  By
Lemma A, `D` is a suitable subgroup of `G_2`; Corollary 5.7 then yields
non-commensurable loxodromic `h_1, h_2 in D` of infinite order with
`E_{G_2}(h_i) = <h_i>` and `{<h_1>, <h_2>} ,->_h G_2`.  These are exactly the
properties of `h_1, h_2` that Hull's argument uses, so the rest of his proof
runs verbatim, now with

    S_{suit} = <h_1, h_2> <= D .

For the record, the steps and where they are unchanged:

* `{<f_1>, <f_2>, <h_1>, <h_2>} ,->_h F` by [Hul16, Lemma 3.5] (§6.6), since
  each is hyperbolically embedded in a free factor and `{G_1, G_2} ,->_h F`.
  Only membership `h_i in G_2` is used, and `D <= G_2`.
* `S_{suit}` is suitable in `F` by [Hul16, Lemma 5.8] (§6.7): it contains the
  infinite order element `h_1` with `<h_1> ,->_h F`, and `<h_1>` is a proper
  subgroup of `S_{suit}` because `h_2` is non-commensurable with `h_1`.
* Apply [Hul16, Theorem 7.1] (§6.2) to `F` with suitable subgroup `S_{suit}`,
  with `{t_1, ..., t_m}` a finite generating set of `G_1`, and with `N` large
  enough that `B_A(N) contains F_1 cup F_2`.  This gives `gamma : F ->> F'`
  with `gamma|_{F_1 cup F_2}` injective (clause (b)) and
  `gamma(t_i) in gamma(S_{suit})` (clause (c)), hence

      gamma(G_1) <= gamma(S_{suit}) <= gamma(D) <= gamma(G_2) ,

  and therefore `F' = <gamma(G_1), gamma(G_2)> = gamma(G_2)`, i.e. `G_2 ->> F'`.
* `gamma(G_1)` is suitable in `F'`: `{<gamma(f_1)>, <gamma(f_2)>} ,->_h F'` by
  [Hul16, Lemma 4.4], then [Hul16, Lemma 5.8].  (Unchanged; uses only
  `f_1, f_2 in G_1`.)
* `F'` is finitely generated, so apply [Hul16, Theorem 7.1] once more, to
  `F'` with suitable subgroup `gamma(G_1)`, with `{t'_j}` a finite generating
  set of `F'`, and with `N'` large enough that the ball contains
  `gamma(F_1 cup F_2)`.  This gives `eta : F' ->> Q` with
  `Q = <eta(t'_j)> <= eta(gamma(G_1))`, hence

      Q = eta(gamma(G_1)) ,

  i.e. `G_1 ->> Q`, and `Q in AH_0`, and `eta` injective on
  `gamma(F_1 cup F_2)`.

Set `alpha_i = eta circ gamma circ iota_i`.  Both are surjective:
`alpha_1` by the last display, `alpha_2` because `G_2 ->> F' ->> Q`.
Clause (i) holds by the two injectivity clauses.  For (ii),

    Q = eta(gamma(G_1)) <= eta(gamma(S_{suit})) <= eta(gamma(D)) = alpha_2(D) <= Q ,

so `alpha_2(D) = Q`.  Clause (iii) is [Hul16, Theorem 7.1(e)] applied to each
of the finitely many applications of Theorem 7.1 in turn (the proof of
Theorem 7.1 handles `m` prescribed elements by `m` successive one-relator
small-cancellation quotients, each satisfying (e); the composite of the
statements "every element of order `n` downstairs lifts to an element of
order `n` upstairs" is again such a statement).  In particular, if `G_1, G_2`
are torsion-free then so is `F = G_1 * G_2`, and then so is `Q`.  Clause (iv):
each application of Theorem 7.1 adds one relator per prescribed element (the
relator `W = t^{-1} h_1^{m_1} h_2^{l_1} ... h_1^{m_n} h_2^{l_n}`, whose set of
cyclic shifts of `W^{\pm 1}` has the same normal closure as `W`), and the
number of prescribed elements is finite at both stages; `F = G_1 * G_2` is
finitely presented, so `Q` is. ∎

*Remark.*  Hull's Corollary 7.4 is the case `D = G_2`, where (ii) is vacuous.
The only content added is Lemma A, which says that the reservoir of
small-cancellation "target words" may be taken inside any prescribed infinite
normal subgroup.

## 5. Proof of Theorems 1 and 2

Apply Theorem B with

    G_1 = H,   G_2 = E,   D = <<S>>^E,   F_1 = {1},   F_2 = {s}

for a fixed `s in S \ {1}`.  The hypotheses hold: `H` and `E` are finitely
presented (hence finitely generated) and torsion-free, so `K(H) = K(E) = {1}`;
`H in AH` because it is a non-elementary hyperbolic group and `E in AH` by
[MO15] (step 2 of §1); `D = <<S>>^E` is normal in `E` and infinite because it
contains the infinite group `S`.

Let `G := Q`, `pi := alpha_2 : E ->> G`.  Then:

* **`G` is torsion-free** — Theorem B(iii), since `H` and `E` are.
* **`G` is finitely presented** — Theorem B(iv).
* **`G` has property (T)** — `alpha_1 : H ->> G` is onto and (T) passes to
  quotients.
* **`pi|_S` is injective** — `pi(s) != 1` by Theorem B(i) with `s in F_2`, and
  `ker(pi) cap S` is a normal subgroup of the simple group `S`, hence trivial.
* **`G = <<pi(S)>>^G`** — by Theorem B(ii),
  `G = pi(D) = pi(<<S>>^E) <= <<pi(S)>>^G <= G`.

This is Theorem 1.  The rest of the Fournier-Facio data survives verbatim,
since it only used that `pi : E ->> G` is onto with `pi|_S` injective:
`Gamma = pi(P)` has (T) and is infinite; `G = <Gamma, t_1, t_2>` with
`t_i Gamma t_i^{-1} <= Gamma`; `J = t_1^{-1} pi(S) t_1` satisfies
`[Gamma, J] = 1` and `t_1 J t_1^{-1} = pi(S) <= Gamma`; and `Gamma cap J = 1`
by the paper's argument (if `(p, s') in <P_1, S> cap ker(pi) <= P_1 x S`, then
for every `x in S` the commutator `[(p,s'),(1,x)] = (1,[s',x])` also lies in
the kernel, so `[s', x] = 1` by injectivity of `pi|_S`, so `s'` is central in
`S`, so `s' = 1`).

For Theorem 2, take the compression core `C` of §2 (`iota` the inclusion of
`Gamma`, `t = t_1`, `c in J \ {1}`) and `K = G`.  By Lemma 0 and Theorem 1,

    C.defectNormal = <<pi(S)>>^G = G = K ,

so `K` is a normal, nontrivial (indeed infinite) subgroup of `G` with property
(T), contained in `C.defectNormal`.  The machine-checked theorem
`normalKazhdan_le_normMFResidual` gives `K <= normMFResidual G`, i.e.
`normMFResidual G = G`: every homomorphism from `G` into the unitary group of
a norm matrix corona kills all of `G`.  Since `G != 1`, no such homomorphism
is injective, so `G` is not MF, and the `¬ IsWeakMF` endpoint applies as
well. ∎

**Consistency check.**  `G` has *no proper subgroup of finite index*.  Indeed
a finite-index subgroup contains a finite-index normal subgroup, and if
`q : G ->> F` is a finite quotient then `q(pi(S))` is a quotient of the
infinite simple group `S`, hence trivial; since `G = <<pi(S)>>`, `q` is
trivial.  This is a necessary feature, not a defect: residually finite groups
are MF, so any non-MF group must fail to be residually finite, and `G` fails
it maximally.  It also confirms that the "finite index" variant of the target
(`[G : <<pi(S)>>] < infinity` with `<<pi(S)>> != G`) is not what the
construction produces: it produces the extreme case `<<pi(S)>> = G`, which is
strictly stronger and needs no inheritance of (T) at all.

**`G` is also non-sofic**, by Fournier-Facio's Proposition 1.2 applied to the
data above, unchanged.  So `G` is a single finitely presented torsion-free
group that is simultaneously non-sofic and non-MF.

## 6. Source-verified citations

Read from the arXiv PDFs via `pdftotext -layout` on 14 August 2026.

### 6.1 [Hul16, Definition 1.4] (arXiv:1308.4345v2)

> Given `G in AH`, a generating set `A` of `G` and a subgroup `S <= G`, we
> will say that `S` is *suitable with respect to `A`* if the following holds:
> 1. `Gamma(G, A)` is hyperbolic and the action of `G` on `Gamma(G, A)` is
>    acylindrical.
> 2. The induced action of `S` on `Gamma(G, A)` is non-elementary.
> 3. `S` does not normalize any finite subgroups of `G`.

By [Hul16, Lemma 5.5], condition 3 is equivalent to `K_G(S) = {1}`, where
`K_G(S)` is the maximal finite subgroup of `G` normalised by `S`; so in a
torsion-free group condition 3 is automatic.

### 6.2 [Hul16, Theorem 7.1 and Corollary 7.4]

> **Theorem 7.1.** Suppose `G in AH` and `S` is suitable with respect to `A`.
> Then for any `{t_1, ..., t_m} subset G` and `N in N`, there exists a group
> `G-bar` and a surjective homomorphism `gamma : G -> G-bar` which satisfy
> (a) `G-bar in AH`.
> (b) `gamma|_{B_A(N)}` is injective.
> (c) `gamma(t_i) in gamma(S)` for `i = 1, ..., m`.
> (d) `gamma(S)` is suitable with respect to `A_0`, where `gamma(A) subset A_0`.
> (e) Every element of `G-bar` of order `n` is the image of an element of `G`
>     of order `n`.

The proof: for `m = 1` and `t = t_1`, Corollary 5.7 provides infinite order
`h_1, h_2 in S` with `{<h_1>, <h_2>} ,->_h (G, A)`; the relator is
`W = t^{-1} h_1^{m_1} h_2^{l_1} ... h_1^{m_n} h_2^{l_n}` and
`G-bar = G / <<R>>` for `R` the set of cyclic shifts of `W^{\pm 1}`; the general
case is induction on `m`.  Hull adds: "Note that we can always choose `N` such
that `B_A(N)` contains any given finite subset of `G`."

> **Corollary 7.4.** Let `G_1, G_2 in AH` with `G_1` finitely generated, `G_2`
> countable.  Then there exists a non-virtually cyclic group `Q` and surjective
> homomorphisms `alpha_i : G_i -> Q` for `i = 1, 2`.  In addition, if `G_2` is
> finitely generated, then we can choose `Q in AH_0`, and if `K(G_i) = {1}`,
> then for any finite subset `F_i subset G_i`, we can choose `alpha_i` to be
> injective on `F_i`.

Its proof, quoted in the parts Theorem B reuses:

> Let `F = G_1 * G_2` ... By Corollary 5.7, there exist infinite order elements
> `f_1, f_2 in G_1` such that `{<f_1>, <f_2>} ,->_h G_1` and infinite order
> elements `h_1, h_2 in G_2` such that `{<h_1>, <h_2>} ,->_h G_2`.  Since
> `{G_1, G_2} ,->_h F`, Lemma 3.5 gives that
> `{<f_1>, <f_2>, <h_1>, <h_2>} ,->_h F`.  Thus, `S = <h_1, h_2>` is suitable in
> `F` by Lemma 5.8.
> Let `t_1, ..., t_m` be a finite generating set of `G_1`.  By Theorem 7.1,
> there exists a group `F'` and a surjective homomorphism `gamma : F -> F'`
> such that `gamma|_{F_1 cup F_2}` is injective and `gamma(t_i) in gamma(S)` for
> each `1 <= i <= m`.  In particular, `gamma(G_1) subset gamma(S) subset gamma(G_2)`.
> ... Since `f_1, f_2 in G_1` and `{<gamma(f_1)>, <gamma(f_2)>} ,->_h F'`, Lemma
> 5.8 gives that `gamma(G_1)` is suitable in `F'`.
> ... Now if `G_2` is finitely generated, then `F'` is finitely generated and we
> can apply Theorem 7.1 to `F'` with a generating set of `F'` as a finite set of
> elements to get `Q` such that the image of `G_1` maps onto `Q`.  Then we will
> also get that `Q in AH` and the image of `G_1` is a suitable subgroup, thus
> `Q in AH_0`.

Note the finitely generated case bypasses Corollary 7.3 (a direct limit) and
uses only two applications of Theorem 7.1 — which is what makes finite
presentability available.

### 6.3 [Osi10, Theorem 2.4] (arXiv:math/0411039)

> **Theorem 2.4.** Let `G` be a group hyperbolic relative to a collection of
> subgroups `{H_lambda}`, `H` a suitable subgroup of `G`, and `t_1, ..., t_m`
> arbitrary elements of `G`.  Then there exists an epimorphism
> `eta : G -> G-bar` such that:
> 1. The group `G-bar` is hyperbolic relative to `{eta(H_lambda)}`.
> 2. For any `i = 1, ..., m`, we have `eta(t_i) in eta(H)`.
> 3. The restriction of `eta` to `union H_lambda` is injective.
> 4. `eta(H)` is a suitable subgroup of `G-bar`.
> 5. Every element of finite order in `G-bar` is an image of an element of
>    finite order in `G`.  In particular, if all hyperbolic elements of `G`
>    have infinite order, then all hyperbolic elements of `G-bar` have infinite
>    order.

Fournier-Facio's citation "[Osi10, Theorem 2.4.5]" is Theorem 2.4, clause 5.
It is the torsion-preservation clause used in step 1 of §1, and it says what
he uses it to say.

### 6.4 [Hul16, Theorem 3.12] (attributed there to [Osi16])

> The following are equivalent: 1. `G in AH`. ... 4. For some generating set
> `A subset G`, `Gamma(G, A)` is hyperbolic and the action of `G` on
> `Gamma(G, A)` is non-elementary and acylindrical.

### 6.5 [Osi16, Lemma 7.1] (arXiv:1304.1246; Trans. AMS 368 (2016) 851--888)

Osin defines: `H <= G` is *s-normal* in `G` if `|H^g cap H| = infinity` for
every `g in G`.  Then:

> **Lemma 7.1.** Let `G` be a group acting acylindrically and non-elementarily
> on a hyperbolic space `S`.  Then every s-normal subgroup of `G` acts
> non-elementarily.

(Its Corollary 1.5 is "the class of acylindrically hyperbolic groups is closed
under taking s-normal subgroups".)  Every infinite normal subgroup is
s-normal, which is the only case Lemma A uses.

### 6.6 [Hul16, Lemma 3.5]

> Suppose `{H_i}_{i=1}^n ,->_h G`, and for each `1 <= i <= n`,
> `{K^i_j}_{j=1}^{m_i} ,->_h H_i`.  Then `{K^i_j} ,->_h G`.

### 6.7 [Hul16, Corollary 5.7 and Lemma 5.8]

> **Corollary 5.7.** Suppose `S` is suitable with respect to `A`.  Then for all
> `k in N`, `S` contains non-commensurable, loxodromic elements `h_1, ..., h_k`
> such that `E_G(h_i) = <h_i>` for `i = 1, ..., k`.  In particular,
> `{<h_1>, ..., <h_k>} ,->_h (G, A)`.

> **Lemma 5.8.** If `S` contains an infinite order element `h` such that `<h>`
> is a proper subgroup of `S` and `<h> ,->_h (G, X)`, then `S` is suitable with
> respect to `A` for some `A supseteq X`.

### 6.8 [Hul16, Theorem 2.3] (Osin's trichotomy)

> Suppose `G` acts acylindrically on a hyperbolic metric space.  Then `G`
> satisfies exactly one of the following: 1. `G` is elliptic. 2. `G` is
> virtually cyclic and contains a loxodromic element. 3. `G` contains
> infinitely many pairwise independent loxodromic elements.

with the note that condition 3 is equivalent to non-elementarity.  (Used only
to read "non-elementary" in Lemma A the same way Hull does.)

## 7. Scope, and what is *not* claimed

* The construction modifies the Fournier-Facio group.  It is **not** asserted
  that the group as published in arXiv:2608.02025 satisfies
  `G = <<pi(S)>>^G`; §3 shows the property cannot be read off from `E`, and
  Hull's corollary as stated does not control it.  What is asserted is that
  the same recipe, with the reservoir of small-cancellation target words
  taken inside `<<S>>^E`, produces a group with the property, at no cost in
  torsion-freeness, finite presentability, property (T), or injectivity on
  `S`.
* No finitely presented simple group with property (T) is used or needed.
  The Ideas section of the claim listed "make `G` simple" as an option and
  warned it was a serious ask; Theorem 1 avoids it entirely — `G` is normally
  generated by `pi(S)` but there is no claim that `G` is simple, and none is
  needed.
* No new small-cancellation estimate is proved.  Theorem B changes *which*
  suitable subgroup is fed to Hull's Theorem 7.1; the small-cancellation
  conditions, and their verification, are Hull's and are untouched.  The only
  ingredient outside Hull's paper is Osin's Lemma 7.1, quoted above.
* Nothing here is formalised.  The analytic half
  (`normal-kazhdan-defect-non-mf`) is machine-checked; the group theory in
  this document is a written argument resting on the source-verified
  statements of §6.

## 8. Addendum (2026-08-14, later): direct route, validation, heredity

* **Direct route.**  `notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md` gives a
  variant of Theorem B that does not re-open Hull's proof of Corollary 7.4:
  apply Theorem 7.1 once, as a black box, to the *published* Fournier-Facio
  group `G`, with suitable subgroup `S_0 = <h_1, h_2>` chosen inside
  `N = <<pi(S)>>^G` by Lemma A + Corollary 5.7 + Lemma 5.8, and with a
  finite generating set of `G` as the prescribed elements.  The output is
  `Q = q(S_0) = q(N)`, 2-generated, finitely presented, torsion-free, AH.
  The single extra input beyond §6 is `G ∈ AH_0`, which the fg clause of
  [Hul16, Corollary 7.4] (quoted in §6.2) already provides when FF's step 3
  is run with that clause invoked.
* **Validation.**  GitHub issue #1 (closed 2026-08-15) records an external
  multi-agent audit of Theorem B's substitution step — Osin suitability,
  in-`D` pair selection, Lemma 3.5 transfer, the two-stage sandwich
  `Q = eta gamma(B) ⊆ eta gamma(T) ⊆ eta gamma(N) ⊆ Q` — and the repo-side
  confirmation of each step.  It also confirms the certification boundary
  choice: cite Hull/Osin/FF for existence, kernel-check everything after
  the routing data (`DefectRoutingData`).
* **Heredity.**  The note strengthens Theorem 2: *every nontrivial quotient*
  `L` of `Q` satisfies `Rad_MF(L) = L` and is nonsofic — the configuration
  descends because `Q = <<q pi(S)>>` forces `q pi(S)` to survive injectively
  in any nontrivial quotient, and `Gamma_L ∩ J_L = 1` follows from
  centrelessness of the simple image alone.  Consequently `Q` is perfect and
  has no proper finite-index subgroup, and its marked presentation with one
  inequation exhibits a nonempty clopen set of 2-marked groups that are
  simultaneously nonsofic and non-MF.

## 9. Adversarial audit, 2026-08-15 — VERDICT: CONFIRMED

This section discharges the audit debt recorded in
`notes/rescue-2026-08-15.md` (item 1): a full walk of §§4–5 and every §6
citation, against fresh downloads of the three source PDFs
(arXiv:1308.4345v2, arXiv:1304.1246, arXiv:2608.02025v1, all re-extracted
via `pdftotext -layout` on 2026-08-15 by a second, independent session).

**Named pressure point 1 — the injectivity clause 7.1(b).**  Verified
against Hull's text.  Clause (b) is `gamma|_{B_A(N)}` injective, and the
paragraph after Remark 7.2 states verbatim: "Note that we can always choose
`N` such that `B_A(N)` contains any given finite subset of `G`."  Both
applications in Theorem B use exactly this: any finite subset of a group
generated by `A` lies in some ball `B_A(N)`, for the *specific* generating
set `A` with respect to which the suitable subgroup was produced (first
application: the `A` from Lemma A via Theorem 3.12(4), transferred through
the free product; second: the `A'` from Lemma 5.8 applied in `F'`).  No
gap.

**Named pressure point 2 — finite presentability of the quotient.**
Verified against Hull's proofs.  Theorem 7.1's proof reduces to `m = 1`
("Clearly it suffices to prove the theorem with m = 1, and the general
statement follows by induction"), and the `m = 1` case sets
`G-bar = G/<<R>>` for `R` the cyclic shifts of the single word
`W = t^{-1} h_1^{m_1} h_2^{l_1} ... h_1^{m_n} h_2^{l_n}` — one relator's
normal closure per prescribed element.  Crucially, Hull's proof of
Corollary 7.4 in the **finitely generated case** reads: "Now if `G_2` is
finitely generated, then `F'` is finitely generated and we can apply
Theorem 7.1 to `F'` with a generating set of `F'` as a finite set of
elements to get `Q` ... Then we will also get that `Q in AH` and the image
of `G_1` is a suitable subgroup, thus `Q in AH_0`."  So the f.g. case uses
exactly two applications of Theorem 7.1 and **bypasses Corollary 7.3's
infinite direct limit** (which is used only for countable, non-f.g. `G_2`).
`F = G_1 * G_2` is finitely presented and each application adds finitely
many relators, so `Q` is finitely presented.  This also confirms the §8
direct-route input: the f.g. clause of Corollary 7.4 delivers `Q in AH_0`
in Hull's own words.

**Every §6 quote checked verbatim** against the sources: Hull Definition
1.4, Theorem 7.1(a)–(e) with the N-note, Corollary 7.4 with its proof,
Corollary 5.7, Lemma 5.8, Lemma 5.5 (noting it is stated for
*non-elementary* `S`, which conditions 1–2 of suitability supply before
condition 3 is evaluated — the order Lemma A uses), Lemma 3.5, Theorem
3.12(4); Osin's s-normal definition, Lemma 7.1 ("Let `G` be a group acting
acylindrically and non-elementarily on a hyperbolic space `S`. Then every
s-normal subgroup of `G` acts non-elementarily."), and Corollary 1.5;
Osin arXiv:math/0411039 Theorem 2.4(5); and the full FF §2 skeleton
including Proposition 1.2's exact hypotheses and the
`Gamma cap J = 1` argument.

**Independent re-derivations** (not just quote-checking): Lemma 0 (both
inclusions, including `pi(S) <= Gamma` from `S <= P` and the
centrelessness step), Lemma A, the substitution's legitimacy (Hull's
Corollary 7.4 proof consumes only: infinite order, non-commensurability,
`{<h_1>,<h_2>} ,->_h G_2`, and membership in `G_2` — Corollary 5.7 applied
to `(G_2, A)` with suitable subgroup `D` supplies all four with
`h_i in D`), the clause (ii) sandwich, the (iii)/(iv) composites, the §5
instantiation (including `E` torsion-free and finitely presented as an HNN
extension of `P` over the finitely generated edge group `P`), and the §8
heredity argument (`Gamma_L ∩ J_L = 1` from centrelessness; Proposition
1.2 descends to every nontrivial quotient).  All correct.

**One erratum found and fixed** (in this document, not in the
mathematics): the former "convention correction" paragraph claimed FF's
paper writes `J = t_1 pi(S) t_1^{-1}`; the actual v1 text writes
`J = t_1^{-1} pi(S) t_1` — the published convention was already the
correct one, and the paragraph has been rewritten so no error is
attributed to the paper.

**Standing scope caveats (unchanged by this audit):** nothing here is
formalised; the argument's trust surface is the quoted published theorems;
`E in AH` via [MO15] is FF's own published step (path of length 2 with
trivial stabiliser, `P_1 cap P_2 = 1` inside `P_1 x P_2 x S`), accepted at
the level of his paper.  The establishment of
`torsion-free-finitely-presented-non-mf` in the research graph may now be
treated as **audited**; external claims should still follow the repo's
formalized-or-explicitly-conditional discipline.
