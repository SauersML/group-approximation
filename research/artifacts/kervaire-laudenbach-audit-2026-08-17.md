# 2026-08-17 — Kervaire--Laudenbach: ingestion audit of an external resolution attempt

Source: a user-supplied external resolution attempt and proof audit,
"Kervaire--Laudenbach: proof audit, reductions, and the exact remaining
obstruction", dated 2026-08-17, unrefereed, written against a snapshot
archive of this repository (`group-approximation-main (66).zip`).  This file
records the ingestion audit and carries the proofs the new graph nodes cite;
the canonical statements live in the graph.

**Headline of the source, which this audit confirms.**  The
Kervaire--Laudenbach conjecture is **not** proved or disproved by the
supplied material, and neither are Whitehead asphericity or Eilenberg--Ganea.
The source says so itself and does not overstate.  What it does produce is a
reduction package: a counterexample, if one exists, can be taken finitely
presented, then two-generator simple, and over a simple coefficient group a
failure is maximally rigid — the whole coefficient group dies and exactly the
cyclic quotient forced by the exponent sum survives.  In that final reduced
form the first-homology obstruction is automatically vacuous.

---

## A. Citation verification status

Read from source **this session** (2026-08-17), quoted verbatim:

* **arXiv:2606.24741v2**, Marimon--Pinsker, *All mixed identities are
  singular in groups with no algebraicity* (submitted 23 June 2026, revised
  10 August 2026).  Full text contains: "it is a major open problem whether
  this phenomenon might occur also for regular words", and "The one-variable
  case of this question is the famous Kervaire-Laudenbach Conjecture,
  answered positively for finite groups and for hyperlinear groups".  This is
  the current-status evidence, and it is exactly the status the graph already
  carries on `kervaire-laudenbach-holds-for-hyperlinear`.
* **arXiv:2303.13728**, Kawauchi, *Kervaire conjecture on weight of group via
  fundamental group of ribbon sphere-link* (submitted 24 March 2023, last
  revised 1 April 2024).  Abstract: "Kervaire conjecture that the weight of
  the free product of every non-trivial group and the infinite cyclic group
  is not one is confirmed by confirming Conjecture Z of a knot exterior."
  Note the statement is **weight one** — the weak conjecture, not coefficient
  injectivity.
* **arXiv:2212.02617**, Kawauchi, *Ribbonness of Kervaire's sphere-link in
  homotopy 4-sphere and its consequences to 2-complexes*.  Abstract: "In the
  use of the smooth unknotting conjecture and the smooth 4D Poincaré
  conjecture, any such sphere-link is shown to be a sublink of a free ribbon
  sphere-link in the 4-sphere", together with the assertion that "the compact
  complement of every ribbon disk-link in the 4-disk is aspherical" and a
  reference to "the Whitehead aspherical conjecture".  The dependency on two
  unresolved smooth four-dimensional conjectures is therefore stated in the
  abstract of the supporting manuscript itself.

**Not** verified this session, and flagged as such wherever a node uses them:

* Schupp, *Embeddings into simple groups*, J. London Math. Soc. (2) **13**
  (1976) 90--94 — every countable group embeds in a two-generator simple
  group.  Classical and not in doubt, but not re-read from the publisher
  here.  See the robustness note in §D: the reduction needs only "nonabelian
  simple", not "two-generator", so a slip in the two-generator refinement
  would not disturb any node.
* Klyachko, arXiv:math/0409146 (the weak conjecture's equivalence with
  unimodular coefficient injectivity); Mikheenko, arXiv:2505.12783; Kulikova,
  arXiv:2402.10531; León Álvarez--Morales, arXiv:2506.10706; arXiv:2605.07853.
  These support the source's status remarks on Whitehead and Eilenberg--Ganea
  and its unimodular scope remark.  The scope remark does not depend on the
  citation — it is re-derived in §B below from the exponent-sum quotients.

**Not re-run this session.**  The source reports rerunning
`experiments/atlas_relator_chart_overlap.py` and quotes `dim A1 = dim A2 = 16`,
`dim (A1 cap A2) = 3`, `|K1 cap K2| = 1`.  Nothing was executed locally here
(standing no-local-execution rule), so those numbers are transcribed, not
reproduced, and no node depends on them.

---

## B. Scope: the nonsingular form is not the weak conjecture

Two statements travel under the same name.

*Weak (Kervaire's original weight form).*  If `G != 1` then
`(G * <t>)/<<w>> != 1`.

*Nonsingular (the form this repository uses, after Nitsche--Thom).*  If
`deg_t(w) = m != 0` then `G -> (G * <t>)/<<w>>` is injective.

For the weak conjecture the degrees `m = 0` and `|m| > 1` are automatic: the
quotient surjects onto `Z` and onto `C_|m|` respectively, by killing `G` and
sending `t` to a generator.  So the entire weak conjecture lives at
`m = ±1`, and Klyachko's equivalence is with **unimodular** coefficient
injectivity.  A proof of the weak conjecture therefore does not, by itself,
deliver injectivity at `|m| > 1`, which is what this repository's
`kervaire-laudenbach-holds-for-hyperlinear` supplies and what
`kl-violating-equation-over-leavitt-unit-group` would have to violate.

The exponent-sum computation above is elementary and is the whole content of
the scope point; it does not rest on the Klyachko citation.

One consequence in this program's favour, worth stating because it cuts the
other way: a **counterexample** at any nonzero degree is enough for
`kl-violation-refutes-hyperlinearity-route`, since the hyperlinear theorem is
the strong form.  The scope caution bites on *importing claimed proofs*, not
on the falsification instrument.

---

## C. Proof: a failure localizes to the coefficient subgroup

Let `A <= G` be generated by the finitely many coefficients occurring in `w`,
and `A_w = (A * <t>)/<<w>>_{A*<t>}`.

Since `A <= G`, `G * <t> = G *_A (A * <t>)`, and imposing `w = 1` inside the
second factor gives the pushout description

    G_w  =  G *_A A_w .

If `A -> A_w` is injective this pushout is an amalgamated free product of two
groups along a common subgroup, so by the normal form theorem `G` embeds in
it.  Contrapositively, if `G -> G_w` is not injective then `A -> A_w` is not
injective.  `A` is finitely generated because `w` is a word.

---

## D. Proof: a counterexample can be taken finitely presented, then simple

Let `A` be a finitely generated counterexample as in §C, `deg_t(w) = m != 0`,
and `1 != a in A` with `a = 1` in `A_w`.  Then in `A * <t>` there is a finite
equality

    a  =  prod_{j=1..r} u_j w^{e_j} u_j^{-1} ,      e_j in {±1}.      (*)

Pick a finite-rank free group `F` and an epimorphism `phi : F ->> A`.  Lift
`a`, every coefficient of `w`, and every `A`-letter of the finitely many
`u_j` to `F`; write `a~, w~, u~_j`.  The defect

    d  =  a~^{-1} prod_j u~_j w~^{e_j} u~_j^{-1}

lies in `ker(phi * id : F * <t> ->> A * <t>)`, which is the normal closure of
`ker phi` in `F * <t>`.  A single element of a normal closure is a finite
product of conjugates of finitely many of its generators, so there are
`r_1, ..., r_k in ker phi` with `d in <<r_1,...,r_k>>_{F*<t>}`.  Put
`P = F/<<r_1,...,r_k>>_F`, which is finitely presented and surjects onto `A`.
Because `(F/<<R>>_F) * <t> = (F * <t>)/<<R>>_{F*<t>}`, the defect dies in
`P * <t>`, so (*) holds there with everything lifted.  The image `a_P` is
nontrivial in `P` (it maps to `a != 1` in `A`) and dies in `P_{w~}`, and
`deg_t(w~) = m != 0`.  So `(P, w~)` is a finitely presented counterexample.

Now embed the countable group `P` into a nonabelian simple group `S` (Schupp;
two-generator if the refinement is used).  Read `w~` in `S * <t>`.  Equation
(*) still holds, so `a_P` — nontrivial in `S`, because the embedding is
injective — dies in `S_{w~}`.  So `(S, w~)` is a counterexample.

**Robustness.**  Only simplicity is used downstream, in §E.  The
two-generator refinement is recorded because it is what the classical theorem
gives, not because anything needs it.

---

## E. Proof: over a simple coefficient group the collapse is total

Let `S` be nonabelian simple, `deg_t(w) = m != 0`, `H = (S * <t>)/<<w>>`.

Let `pi_m : S * <t> -> C_m` kill `S` and send `t` to a generator, and let
`N_m = ker pi_m = { x : m divides deg_t(x) }`.  The description of `N_m` by
degree is independent of which generator `t` is sent to, since the generators
of `C_m` are the `t-bar^j` with `gcd(j, m) = 1`.

*(i) Failure forces `H = C_|m|`.*  `ker(S -> H)` is normal in `S` and
nontrivial by hypothesis, so it is all of `S` and the image of `S` in `H` is
trivial.  Then `H` is generated by the image of `t` alone, and `w = 1` reads
`t^m = 1`, so `H` is a quotient of `C_|m|`.  Conversely `pi_m` kills `w`
(exponent sum `m`), so it factors through `H`, giving `H ->> C_|m|`.  A
quotient of `C_|m|` surjecting onto `C_|m|` is `C_|m|`.

*(ii) Failure is exactly one-element normal generation.*  If `S -> H` fails
then by (i) the quotient map `S * <t> -> H = C_|m|` kills `S` and sends `t`
to a generator, so its kernel is `N_m`; that kernel is `<<w>>`.  Hence
`N_m = <<w>>_{S*<t>}` with `deg_t(w) = m`.

*(iii) The converse direction needs no simplicity.*  For **any** nontrivial
group `G` and any `w in N_m` with `deg_t(w) = m`, if
`N_m = <<w>>_{G*<t>}` then `G_w = (G * <t>)/N_m = C_m`, so every element of
`G` dies and `(G, w)` is a counterexample.

So for two-generator simple `S`, Kervaire--Laudenbach over `S` is exactly:

    for every m >= 1 and every w in N_m with deg_t(w) = m,
    <<w>>_{S*<t>}  is a proper subgroup of  N_m .

**Correction to the source.**  The source states the equivalence only for
simple `S`.  Direction (iii) holds for every nontrivial coefficient group,
which is what makes the normal-generation formulation usable over the binary
Leavitt unit group — a group this repository knows to be perfect but does not
know to be simple.

---

## F. Proof: the first-homology test is vacuous in the reduced form

Let `S` be any group, `m >= 1`, `N_m = ker(S * <t> -> C_m)` as above.

*Structure.*  `S * <t>` is the fundamental group of a graph of groups with a
single vertex group `S` and one loop with trivial edge group.  The index-`m`
subgroup `N_m` corresponds to the `m`-fold cyclic cover: `m` vertices,
carrying `t^i S t^{-i}` for `0 <= i < m`, and `m` edges forming a cycle, of
first Betti number `1`.  Hence

    N_m  =  ( *_{i=0}^{m-1} t^i S t^{-i} )  *  <t^m> ,

with `<t^m>` infinite cyclic.  (Equivalently: Reidemeister--Schreier with
transversal `1, t, ..., t^{m-1}`.)

*Consequence for perfect `S`.*  Abelianizing,
`N_m^ab = (+)_{i<m} S^ab (+) Z`, and `S^ab = 1` when `S` is perfect, so
`N_m^ab = Z`, generated by `[t^m]`.  The homomorphism `x |-> deg_t(x)/m`
induces this isomorphism, so **every** `w in N_m` with `deg_t(w) = m` has
`[w] = ±1`, a generator.  Conjugation preserves `deg_t`, so the residual
`C_m`-action on `N_m^ab` is trivial.

*The vacuity.*  If `N_m = <<w>>_{S*<t>}` then, since inner automorphisms of
`N_m` act trivially on `N_m^ab` and `S <= N_m`, the class `[w]` generates
`N_m^ab` as a `Z[C_m]`-module.  That necessary condition is therefore
satisfied by every candidate word, automatically, for every perfect `S`.
A first-Fox-derivative or Alexander-module computation in this reduced
setting selects nothing and excludes nothing.

**Correction to the source.**  The source calls `N_m^ab` "the relation
module".  The relation module of a presentation is
`<<w>>/[<<w>>,<<w>>]`; the object computed here is `N_m^ab`, and the
necessary condition it kills is precisely "`[w]` generates `N_m^ab` over
`Z[C_m]`".  The conclusion is unaffected, and it is the conclusion that the
graph records.

*Where the obstruction must live instead.*  Anything that sees more than
`H_1` of the kernel: a Peiffer quotient or crossed module, identities among
relations, a second relation module or explicit `pi_2` class, or a finite
**nonabelian** quotient of `N_m`, compatible with the ambient conjugation
action, in which the image of `w` has proper normal closure.

---

## G. Proof: a counterexample absorbs any prescribed countable group

If `(G, w)` is a counterexample and `A` is countable, then `w in G * <t>`
gives

    (G * A * <t>)/<<w>>  =  A * G_w ,

so the coefficient of `G` that died still dies, and it is still nontrivial in
`G * A`.  Applying §D to the countable group `G * A` produces a
(two-generator) simple counterexample containing `A`.

Consequence: no criterion phrased in terms of which countable groups a
coefficient group does or does not contain — torsion spectrum, excluded
subgroups, amenable subgroups, local finiteness — can separate the possible
counterexamples from the impossible ones.

---

## H. Which failed routes are theorems and which are only difficulties

The source's §8 mixes two kinds of statement.  Only the first kind became an
invalidating claim in the graph.

**Proved obstructions (now claims).**

1. *Near-identity filtration.*  Let `R` be a ring with two-sided ideals
   `R > I > I^2 > ...`, `I^r I^s <= I^{r+s}` and `∩_n I^n = 0`, and let
   `G <= (1 + I) ∩ R^x`.  Then `[1 + I^r, 1 + I^s] <= 1 + I^{r+s}`, so
   `gamma_n(G) <= 1 + I^n` and `∩_n gamma_n(G) = 1`: `G` is residually
   nilpotent.  A nontrivial perfect group has `gamma_n(G) = G` for all `n`,
   so it admits no faithful such representation — and §D sends every
   counterexample into a simple, hence perfect, group.  Magnus/power-series
   fixed-point constructions that place the coefficients near `1` cannot be
   universal.
2. *Block-monomial roots.*  Over a decomposition into blocks indexed by `J`,
   the block-monomial invertibles map homomorphically onto `Sym(J)`.
   Block-diagonal coefficients go to the identity and a root `T` with
   underlying permutation `sigma` goes to `sigma`, so `w(T)` goes to
   `sigma^m`.  Thus `w(T) = 1` forces `sigma^m = 1`, and at `m = ±1` forces
   `sigma = 1`: a bilateral shift or other Hilbert-hotel rearrangement
   contributes nothing at unimodular degree.
3. *Ambient room is not a root.*  A faithful `rho : G -> U(H)` together with
   `T in U(H)` satisfying `w(rho, T) = I` **is** a representation of `G_w`
   faithful on `G`, and conversely `G -> G_w` supplies one via the regular
   representation of `G_w`.  Likewise an existentially closed overgroup
   solves exactly the finite systems already consistent with the coefficient
   diagram, and that consistency is the conjecture.  Neither enlargement is a
   reduction.

**Identified difficulties, not theorems (recorded in node bodies, no
invalidation).**

4. Strong-operator local approximation lacks two-sided metric control: a
   finite-dimensional root can move test vectors outside the window on which
   coefficient multiplication was controlled.  This is where the hyperlinear
   proof's tracial `‖·‖_2` does the work, and it is a gap in the alternatives,
   not a proof that they fail.
5. For a general state `phi`, `‖x‖_{2,phi}` "need not" have a conjugation-
   stable two-sided null ideal.  "Need not" is not "does not"; no theorem is
   claimed here and none is recorded.
6. Binate/acyclic swindles preserve homology but are not known to preserve a
   prescribed finite set of coefficient inequations; the compactness
   statement that would make them work is essentially the conjecture.
7. Split-variable and diagrammatic-reducibility strategies stall because
   asphericity of the shape complex is weaker than relative diagrammatic
   reducibility.

---

## I. What this changes in this repository

* The graph gains a root, `kervaire-laudenbach-nonsingular-conjecture`, with
  the reduction chain beneath it and five obstruction claims killing five
  attacks.
* The existing falsification lane
  (`kl-violating-equation-over-leavitt-unit-group` →
  `kl-violation-refutes-hyperlinearity-route` → `non-hyperlinear-group`) gains
  one **sufficient** target — a degree-`m` word normally generating
  `ker(R^x * Z -> C_m)` — and loses two attacks: any first-homology
  certificate (§F, since `L_k(1,2)^x` is perfect by
  `leavitt-gl-equals-el-and-perfect-unit-group`), and any screening of
  candidate groups by their subgroup structure (§G).
* Nothing here bears on Q3.4 in either direction, and nothing here weakens
  `kervaire-laudenbach-holds-for-hyperlinear`, which remains the reason the
  lane exists at all.

## J. What was checked in the repository and found absent

The source audited `research/kervaire-laudenbach-holds-for-hyperlinear.md`,
`research/kl-violating-equation-over-leavitt-unit-group.md`,
`research/kl-violation-refutes-hyperlinearity-route.md`,
`notes/EXPLICIT_LEAVITT_ATLAS.md`,
`research/leavitt-gl-equals-el-and-perfect-unit-group.md`, and the atlas
extraction notes, and reports no hidden proof of Kervaire--Laudenbach,
Whitehead asphericity, or Eilenberg--Ganea.  Two of its incidental
observations are correct and worth keeping on the record here: the files
named "Whitehead" in the Lean development are algebraic `K_1` Whitehead
groups, unrelated to the asphericity conjecture, and
`GroupApproximation/Steinberg/KervaireSteinberg.lean` is not a formalization
of the conjecture.
