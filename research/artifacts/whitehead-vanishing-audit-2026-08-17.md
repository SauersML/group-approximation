# 2026-08-17 — Whitehead vanishing for torsion-free groups (ingestion audit)

Source: a user-supplied external resolution attempt, "Whitehead-Group
Vanishing for Torsion-Free Groups: Resolution Attempt and Proof Audit",
dated 2026-08-17, unrefereed.  It was written against a snapshot archive
(`group-approximation-main (66)(1).zip`, SHA-256
`df9777b5e3f92412cae97d5e7067b9db6c0c20dbfacdda937d74405213a3efb7`) and
audits this repository's `K_1` and universal-group code.  This file records
the ingestion audit and carries the proofs the new graph nodes cite; the
canonical statements live in the graph.

**Headline of the source, which this audit confirms.** The Whitehead
vanishing conjecture — `Wh(G) = 0` for every torsion-free `G`, Conjecture 3.6
of Lueck's Farrell--Jones survey (arXiv:2507.11337, statement read from
source this session: "Let G be a torsionfree group. Then Wh(G) vanishes") —
is **not** proved or disproved by the supplied material.  Every route in this
repository stops on the wrong side of one of three boundaries: a Leavitt
algebra is not `ZG`; topological `K_*` of a `C*`-algebra is not algebraic
`K_*` of `ZG`; and a group embedding is not an injection on `Wh`.

**Four corrections this audit makes to the source.**  Three strengthen it,
one is a genuine error it inherited from the graph.

1. **The torsion-free Higman embedding is a theorem, not a gap.**  The source
   says (its Section 5.4) that "no such result is proved in the supplied
   repository or in the cited torsion-preserving embedding work," and its
   Theorem 5.2 invokes an unnamed "torsion-preserving form of Higman
   embedding."  Chiodo, arXiv:1107.1489v4, **Theorem 2.2** — read from source
   this session — is exactly that theorem.  See the citation record below.
   This closes a hole that has been open in this graph
   (`torsion-free-higman-embedding`), independently of anything Whitehead.
2. **The reduction goes one step further than the source takes it**, to
   *finitely generated recursively presented* torsion-free groups, and the
   step needs none of the inequation apparatus of the source's Corollary 5.3.
   Section C below.  This matters: it means the source's own proposed missing
   bridge, which is stated for exactly that class, really would suffice.
3. **The source's corrected `K_0` computation for the matrix corona is right,
   and this graph had the uncorrected version in two established nodes.**
   Section E below.
4. **The source's Gardam remark is correctly attributed** (the summariser
   consulted first got this wrong).  Gardam, arXiv:2312.05240v2 Theorem A,
   read from source: the group is `P = <a,b | b^-1 a^2 b = a^-2,
   a^-1 b^2 a = b^-2>`, the Promislow/Hantzsche--Wendt group, torsion-free
   with index-4 subgroup `Z^3`.  Section F below.

## Audit table

Mapping from the source's numbering to graph nodes.  Everything below was
checked line by line unless marked otherwise.

| Source | Verdict | Node |
|---|---|---|
| Thm 2.1 (`Wh` = assembly cokernel) | correct; folklore, no novelty | `whitehead-is-degree-one-assembly-cokernel` |
| Cor 2.2, Cor 2.3 | correct; restatements | in that node's body |
| Thm 3.1 (one test group) | correct; elementary packaging | `whitehead-vanishing-universal-test-group`, `whitehead-class-supported-on-finitely-generated-subgroup` |
| Prop 4.1, 4.2 (augmentation) | correct | `augmentation-blocks-unital-leavitt-family` |
| Sec 4.1 (Lean audit) | confirmed against live `main` | below |
| Prop 5.1 (coded coordinates) | correct; already how the Lean file reads | not noded (special case of Thm 3.1's split) |
| Thm 5.2, Cor 5.3 (pattern realization) | correct, **once Chiodo Thm 2.2 supplies its cited input** | `finite-torsion-free-pattern-realizable-finitely-presented` |
| Sec 5.4 (the missing bridge) | correct as a gap; **misstates the literature** (see 1 above) | `whitehead-injective-torsion-free-embedding` |
| Thm 6.1 (corona `K`-theory) | correct, and corrects this graph | `matrix-corona-product-k0-is-rank-bounded-sequences` |
| Prop 6.2 (zero detector) | correct | `topological-k1-cannot-detect-integral-whitehead` |
| Sec 7.1 (nonsofic/non-MF) | correct; no implication either way | in the obstruction bodies |
| Sec 7.2 (exotic units) | correct; attribution verified | Section F below |
| Sec 9 (certificates) | correct | root claim body |

---

## A. `Wh` is the cokernel of the degree-one assembly map

**Statement.** For every group `G`, with no torsion hypothesis,

    Wh(G)  ==  coker( A_1^G : H_1(BG; K(Z)) -> K_1(ZG) ).

**Proof.**  `BG` is connected, so the basepoint splits `BG_+ ~ S^0 v BG`
stably, giving

    H_1(BG; K(Z))  ==  K_1(Z)  (+)  H~_1(BG; K(Z)).

Run the Atiyah--Hirzebruch spectral sequence `E^2_{p,q} = H~_p(BG; K_q(Z))`
converging to `H~_{p+q}(BG; K(Z))`.  `Z` is regular, so `K_q(Z) = 0` for
`q < 0` (Bass--Heller--Swan), and `K_0(Z) = Z`.  In reduced total degree one
`p >= 1`, so the only surviving term is

    E^2_{1,0} = H~_1(BG; Z) = G_ab.

No differential touches it: an incoming `d_r` starts at bidegree
`(1+r, 1-r)` with coefficients `K_{1-r}(Z) = 0` for `r >= 2`, and an outgoing
`d_r` lands in negative `p`.  Hence `H~_1(BG; K(Z)) = G_ab` and

    H_1(BG; K(Z))  ==  C_2  (+)  G_ab,      C_2 = K_1(Z) = {+-1}.

On the first summand the assembly is induced by `Z -> ZG` and hits `[-1]`.
On the second, the class of `g` is represented by `S^1 = BZ -> BG`, `1 |-> g`;
naturality reduces to `G = Z`, where under Bass--Heller--Swan for
`Z[t,t^-1]` the circle's `K_0(Z)`-generator maps to the Laurent unit `t`.  So
the image of `g` is `[g]`.  Therefore

    im(A_1^G) = < [-1], [g] : g in G > = < [+-g] >,

and the cokernel is the defining quotient of `Wh(G)`.  QED

**Priority.**  Folklore.  This is the trivial-family case of the standard
assembly picture and is why `Wh` is *defined* by that quotient; Lueck's
survey states Conjecture 3.6 as "Farrell--Jones Conjecture for Wh(G) for
torsionfree G" and lists the Farrell--Jones class (hyperbolic groups, finite
dimensional CAT(0)-groups, lattices, 3-manifold groups, S-arithmetic groups)
as the known cases.  The survey does not display the cokernel identity in the
form above, but nothing here is new and no novelty should be claimed.  The
value is the sharpening: the source of `A_1^G` is *completely known*, so the
conjecture asserts exactly that no degree-one class exists beyond the scalar
and loop classes.

## B. Finite generation of the support of a Whitehead class

**Statement.** For any group `G` and any `x` in `Wh(G)` there is a finitely
generated subgroup `H <= G` and `y` in `Wh(H)` with `y |-> x`.  If `G` is
torsion-free so is `H`.

**Proof.**  Represent `x` by `A` in `GL_m(ZG)` and put `B = A^-1`.  Only
finitely many elements of `G` occur in the coefficients of the entries of `A`
and of `B`.  Let `H` be the subgroup they generate: finitely generated, and
torsion-free whenever `G` is.  Both matrices already lie in `M_m(ZH)` and
`AB = BA = I_m` holds there, so `A` defines a class in `Wh(H)` mapping to
`x`.  QED

## C. Reduction to finitely generated recursively presented groups

This is Section C of the audit rather than of the source: it is sharper than
the source's Theorem 3.1 and its Corollary 5.3, and it is what makes the
source's proposed bridge sufficient rather than merely necessary.

**Statement.** Suppose `Wh(K) = 0` for every finitely generated recursively
presented torsion-free group `K`.  Then `Wh(G) = 0` for every torsion-free
`G`.

**Proof.**  Let `G` be torsion-free and `x` in `Wh(G)`, represented by `A` in
`GL_n(ZG)` with `B = A^-1`.  Let `S` be the finite set of group elements
occurring in the entries of `A` and `B` (Section B), and let
`T = {1} u S u S.S`, also finite.

Let `P` be the group with one generator `x_t` for each `t` in `T` and the
finitely many relations

    x_1 = 1,      x_s x_s' = x_{ss'}      for all (s,s') in S x S.

`P` is finitely presented, and `phi : P -> G`, `x_t |-> t`, is a well-defined
homomorphism because every imposed relation holds in `G`.

Let `Ahat`, `Bhat` in `M_n(ZP)` be obtained from `A`, `B` by replacing each
coefficient `s` in `S` by `x_s`.  In `ZG` the entry `(AB)_{ik}` is a sum over
pairs `(s,s')` of terms supported at the products `ss'`, and like terms
combine exactly when the products agree in `G`.  In `ZP` the relations force
`x_s x_s' = x_{ss'}`, so the same sum is supported at the labels `ss'` and
like terms combine under exactly the same condition.  The two coefficient
collections are therefore identical, and `(AhatBhat)_{ik} = delta_{ik} x_1 =
delta_{ik}`.  Symmetrically `BhatAhat = I_n`.  So `Ahat` is in `GL_n(ZP)`.

Now let `Ptf = P / Tor_oo(P)` be the torsion-free universal quotient
(Chiodo Cor 3.4; recursively presented by Chiodo Prop 3.8).  `Ptf` is
finitely generated, being a quotient of `P`, and torsion-free.  Since `G` is
torsion-free, `phi` factors as `P -> Ptf ->^psi G` by the universal property.
Let `Atilde` be the image of `Ahat` in `M_n(Z Ptf)`; functoriality makes it
invertible, and `psi_*[Atilde] = [A] = x` in `Wh(G)`.

By hypothesis `Wh(Ptf) = 0`, so `[Atilde] = 0` and hence `x = 0`.  QED

**Two remarks.**  First, no inequations are needed: the source's Corollary
5.3 carries a set `W` of nontrivial differences precisely because it aims at
a *finitely presented* overgroup, where the comparison homomorphism points
the wrong way and faithfulness must be bought.  Stopping at `Ptf` the map
`psi : Ptf -> G` points the right way and plain functoriality suffices.
Second, this closes a gap the source leaves open without noticing it: its
Theorem 3.1 reduces to finitely *generated* torsion-free groups, of which
there are continuum many and only countably many are recursively presented,
so a bridge quantified over recursively presented groups would not obviously
cover the reduction.  It does, by the above.

## D. The augmentation obstruction

**Statement (unital form).**  A unital ring `R` admitting a unital ring
homomorphism `eps : R -> Z` contains no binary Leavitt family, i.e. no
`s_0, s_1, t_0, t_1` with `t_i s_j = delta_{ij}` and `s_0t_0 + s_1t_1 = 1`.

**Proof.**  Put `a_i = eps(s_i)`, `b_i = eps(t_i)` in `Z`.  From `t_0s_0 = 1`,
`b_0a_0 = 1`, so `a_0, b_0` are units of `Z`.  From `t_0s_1 = 0`,
`b_0a_1 = 0`, so `a_1 = 0`.  But `t_1s_1 = 1` gives `b_1a_1 = 1`, a
contradiction.  (The idempotent relation is not needed.)  Any `ZG` carries
the augmentation `sum n_g g |-> sum n_g`.  QED

**Statement (finite-matrix form).**  For every group `G` and every finite
`n >= 1`, `M_n(ZG)` contains no unital binary Leavitt family.

**Proof.**  Apply entrywise augmentation `M_n(ZG) -> M_n(Z)` and extend
scalars to `Q`.  `T_0S_0 = I_n` on the finite-dimensional space `Q^n` makes
`S_0` invertible with `T_0 = S_0^-1`; then `T_0S_1 = 0` forces `S_1 = 0`,
contradicting `T_1S_1 = I_n`.  QED

**Consequence.**  The repository's `K_1(L_k(1,2)) = 0` cannot be transported
to `K_1(ZG)` by locating Leavitt generators in `ZG` or in any `M_n(ZG)`: the
defining self-similarity `R = R (+) R` is unavailable there, and it is what
powers the swindle.  A nonunital family in a corner `p M_n(ZG) p` with
augmented rank zero is not formally excluded, but exhibiting a nonzero such
corner is itself a hard statement about idempotents over `ZG`.

## E. Corona `K`-theory, corrected

Write `A = prod_n M_{d_n}` (bounded product), `I = (+)_n M_{d_n}` (`c_0`
sum), `Q = A/I`, and

    L(d) = { (z_n) in prod_n Z : sup_n |z_n| / d_n < oo }.

**Statement.**

    K_0(A) = L(d)          K_1(A) = 0
    K_0(I) = (+)_n Z       K_1(I) = 0
    K_1(Q) = 0             K_0(Q) = L(d) / (+)_n Z.

**Proof.**  A projection in `M_k(A) = prod_n M_{k d_n}` is a sequence `(p_n)`
of projections; two are Murray--von Neumann equivalent iff their ranks agree
coordinatewise, the intertwiners being assembled coordinatewise with norm
one.  The realizable rank sequences at stabilization level `k` are exactly
those with `0 <= r_n <= k d_n`.  **One `k` must work for the whole
sequence**, so the projection monoid is the set of rank sequences with
`sup r_n/d_n < oo`, and its Grothendieck group is `L(d)`, not `prod_n Z`.
For `I`, a projection sequence that is norm-null has finitely many nonzero
coordinates, since a nonzero projection has norm one; so `K_0(I) = (+)_n Z`,
and the map to `K_0(A)` is the inclusion `(+)_n Z <= L(d)`, injective.
For `K_1(A)`: each unitary `u_n` in `M_{kd_n}` is `exp(i h_n)` with
`||h_n|| <= pi` by finite-dimensional functional calculus, so `h = (h_n)`
is in `M_k(A)` and `t |-> exp(ith)` is a norm-continuous path from `1` to
`u`; `K_1(A) = 0`.  `I` is an inductive limit of finite direct sums of matrix
algebras, so `K_1(I) = 0`.  The six-term sequence
`0 = K_1(A) -> K_1(Q) -> K_0(I) -> K_0(A)` then has the index map both
injective (exactness on the left) and zero-image (the right map is
injective), so `K_1(Q) = 0`; and `K_0(I) -> K_0(A) -> K_0(Q) -> K_1(I) = 0`
gives `K_0(Q) = L(d)/(+)_n Z`.  QED

**Effect on this graph.**  `L(d) = prod_n Z` fails whenever `d_n` does not
dominate arbitrary integer growth — for `d_n = 1`, `K_0(A)` is the *bounded*
sequences.  Two established nodes carried the wrong identification:

* `matrix-corona-k1-vanishes-proof` used `K_0(prod) = prod Z` as an
  intermediate step.  The conclusion is unaffected — all that is needed is
  injectivity of `(+)_n Z -> K_0(A)`, and finitely supported sequences are
  trivially in `L(d)`.  Corrected in place and rewired to require the new
  claim.
* `matrix-corona-k0-index-survives` had `K_0(Q) = prod Z / (+) Z` **in its
  statement**.  Corrected to `L(d)/(+)_n Z`.  Its intended content survives
  intact and is in fact sharpened: the Bott index of an almost-commuting
  pair in `M_{d_n}` is a difference of ranks in `M_{d_n}`, so it is bounded
  by `d_n` and the resulting index sequences land in `L(d)` automatically.
  The group is still enormous, so relative index arguments remain live.

**Statement (zero detector).**  `K_1^top(Q) = 0` implies nothing about
`K_1^alg(ZG)` or `Wh(G)` for a group represented in `Q`.  A representation
`G -> U(Q)` induces `K_1^alg(ZG) -> K_1^alg(Q) -> K_1^top(Q) = 0`, so the
composite annihilates every class, zero or not; a zero-valued invariant
witnesses nothing.  The warning example is `G = Z^2`: `C*(G) = C(T^2)` has a
nontrivial reduced topological `K_0` (the Bott class) while
`K~_0^alg(Z[Z^2]) = 0` and `Wh(Z^2) = 0` by Bass--Heller--Swan.  Analytic
classes need not come from algebraic ones, in either direction.

## F. Exotic units are not Whitehead classes

Gardam, arXiv:2312.05240v2, "Non-trivial units of complex group rings",
Theorem A, read from source this session.  The group is

    P = < a, b | b^-1 a^2 b = a^-2,  a^-1 b^2 a = b^-2 >,

the Promislow group: a group of affine isometries of `R^3`, torsion-free,
with the index-4 subgroup `<x,y,z> = Z^3` where `x = a^2`, `y = b^2`,
`z = (ab)^2`.  The unit has coefficients in `Z[zeta_8]`, and the paper says
explicitly: "We have not succeeded in finding a non-trivial unit in `Z[P]`
but note that the coefficients in the theorem are at least algebraic
integers."

So the counterexample is not even a candidate integral class, and separately
`P` is torsion-free virtually `Z^3`, hence torsion-free
poly-(finite or cyclic), so `Wh(P) = 0` by Farrell--Hsiang (JLMS (2) 24
(1981) 308--324; **cited at abstract level, not read**), and independently
`P` is a finite-dimensional CAT(0)-group and therefore in Lueck's
Farrell--Jones class.  A torsion-free group can carry exotic units over a
coefficient field and still have vanishing Whitehead group; the two
phenomena are unrelated.

## G. Lean audit, re-run against live `main`

The three files the source names are present, tracked, and — checked this
session, which the source could not do — all three are imported by the root
`GroupApproximation.lean` (lines 749, 756, 757), so they are inside the
`lake build` closure and are actually elaborated rather than merely
committed.

    GroupApproximation/KOne/ClassicalKOne.lean
      SHA-256 332cbc0e15ff4b49d6c32c2f51e12f082b6b61bd4803f2455d541d3da0b664ae
    GroupApproximation/Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean
      SHA-256 ec59a6aa45b237a4496bbd6ea7b8d1279872f9aed46debb68acf176e9f3177ed
    GroupApproximation/KOne/WhiteheadQuotient.lean

Both source hashes match the live tree, so the snapshot was not stale for
these files.  What the code proves, and what it does not:

* `binaryLeavittClassicalK1_subsingleton` — `K_1(L_k(1,2)) = 0` in the
  classical `colim GL_n / E_oo` form, over every field.
* `binaryLeavittWhiteheadK1_subsingleton` — the rank-one quotient
  `L^x / stableUnits L` is trivial.  Its own docstring already says this is
  "the rank-one Whitehead quotient", contrasted with the classical form; the
  name is a quotient construction for the Leavitt algebra and **is not** the
  Whitehead group of a group.  The source's reading is correct and the file
  does not overclaim.
* `UniversalFinitelyPresentedTorsionFreeGroup` — countable, torsion-free,
  with injective coordinate inclusions and evaluations, and every finitely
  presented torsion-free group appearing as a coordinate.  Despite the
  identifier this is a universal payload *for* finitely presented
  torsion-free groups; the file does not claim the product is finitely
  presented, and does not claim Chiodo's Theorem 3.9 (which would give a
  finitely presented torsion-free group containing every countably generated
  recursively presented torsion-free group).

Neither `K_1` result is a statement about `K_1(ZG)`, and Section D shows the
gap is not a matter of finding the right embedding.

## H. Citation record: Chiodo, arXiv:1107.1489v4

Read from source this session (pages 1--8 of the PDF), because it closes a
standing hole in this graph.

* **Theorem 2.2.** "There is a uniform algorithm that, on input of a
  countably generated recursive presentation `P = <X|R>`, constructs a finite
  presentation `T(P)` such that `P- ↪ T(P)` and `Tord(P-) = Tord(T(P))`,
  along with an explicit embedding `phi- : P- ↪ T(P)`."  Here `Tord(G)` is
  the set of orders of nontrivial torsion elements (Definition 2.1).  Chiodo
  attributes it to [4, Lemma 6.9 and Theorem 6.10] and notes it is implicit
  in Rotman's proof ([13] Theorem 12.18) of Higman embedding.
  **Taking `Tord(P-) = empty` gives the torsion-free Higman embedding
  outright**: every recursively presented torsion-free group embeds in a
  finitely presented torsion-free group.
* **Definition 3.1, Lemma 3.2, Prop 3.3, Cor 3.4.** `Tor_oo(G) = union_i
  Tor_i(G)` with `Tor_{i+1}(G)` the normal closure of the elements mapping
  into `Tor(G/Tor_i(G))`; `G/Tor_oo(G)` is torsion-free, equals the
  torsion-free radical quotient `G/rho(G)`, and is the universal torsion-free
  quotient `G^tf`.
* **Lemma 3.7, Prop 3.8.** `Tor_oo` is r.e. for a countably generated
  recursive presentation, and there is a uniform algorithm producing a
  recursive presentation `P^tf = <X | R'>` of `G^tf` on the same generators.
* **Theorem 3.9.** "There is a finitely presentable group `G` which is
  torsion free, and contains an embedded copy of every countably generated
  recursively presentable torsion-free group."
* **Theorem 3.10.** The universal finitely presented torsion-free group: `G`
  torsion-free such that for finitely presented `H`, `H ↪ G` iff `H` is
  torsion-free.  Chiodo notes this first appeared in Belegradek's appendix to
  [1], Theorem A.1.

This supersedes the "literature-plausible, not verified at theorem level"
status the graph carried on `torsion-free-higman-embedding`, and supersedes
its warning that Belegradek "was not read": the claim no longer rests on
Belegradek at all, only on Chiodo Theorem 2.2, which is read and quoted here.
The source document's Section 5.2 note — that Chiodo--Hill is a
finitely-presented-to-finitely-presented statement — is correct but
irrelevant once Theorem 2.2 is on the table.

**What this does *not* close.**  Chiodo gives an embedding, and nothing about
`K_1`.  `Wh(K) -> Wh(H)` need not be injective for it, and a *retraction*
would be too strong to ask for in general, since a retract of a finitely
presented group is finitely presented while the source groups here need not
be.  That gap is `whitehead-injective-torsion-free-embedding` and it is the
whole of what stands between this graph and the finitely-presented route.

## I. What a resolution certificate must contain

Unchanged from the source, and recorded on the root claim:

*Proof side.*  For every torsion-free `G` and every `A` in `GL_n(ZG)`, a
factorization `A (+) I_r = E_1 ... E_m diag(+-g, 1, ..., 1)` with each `E_i`
elementary; equivalently, surjectivity of `A_1^G`.  A route through finitely
presented groups must additionally prove injectivity on the relevant
Whitehead class, or return the factorization along a homomorphism.
Transplanting the finite support pattern is not enough.

*Disproof side.*  A torsion-free `G`, a matrix `A` in `GL_n(ZG)` with an
exact inverse, and an invariant `tau` on `K_1(ZG)` vanishing on elementary
matrices and on every `[+-g]` with `tau([A]) != 0`.  No route in this
repository furnishes such a `tau`; the matrix corona supplies a *zero* target
(Section E), which is the opposite of a detector.

Nonsoficity and non-MF-ness are not inputs to either side.  They are
matrix-approximation properties of a group or its operator images; Whitehead
vanishing is a quotient calculation in algebraic `K`-theory over `Z`.  No
implication in either direction is proved anywhere in this corpus or in the
cited literature.  Failure of soficity does not even give failure of direct
finiteness of `ZG`, and a one-sided inverse would concern a different
conjecture and would not produce a `K_1` class at all, since `K_1`
representatives must be genuinely invertible.
