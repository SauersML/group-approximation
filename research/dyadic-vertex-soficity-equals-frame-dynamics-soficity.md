---
rg: 2
id: dyadic-vertex-soficity-equals-frame-dynamics-soficity
kind: claim
title: The dyadic vertex action is sofic iff the uniquely ergodic frame dynamics on a compact quotient is sofic iff twin deep modular models exist
distinct_from:
  homogeneous-quotient-soficity-gives-vertex-soficity: that proves one implication for general totally disconnected pairs along a lattice tower; this proves the converse for the dyadic pair, and shows that a single lattice suffices.
  twin-deep-vertex-models-give-homogeneous-microstates: that proves that twin deep models give microstates; this closes the circle, since any sofic model of the vertex action yields twin deep models.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that uses the generalized Bernoulli shift over A/C as the measured shadow of the vertex action; this identifies a different, compact algebraic system whose soficity is exactly equivalent to it.
---

**ESTABLISHED (unreviewed).** Let `A = PSL_2(Z[1/2])`, `C = PSL_2(Z)`, `L = PSL_2(Q_2)`. The
following are equivalent.

1. The coset action `A ↷ A/C` (one colour class of vertices of the `3`-regular tree) is sofic
   (GKP Definition 2.1(5)).
2. For every `R >= 2` and `ε > 0` a twin deep model `(TD_(R,ε))` exists, as in
   `twin-deep-vertex-models-give-homogeneous-microstates`.
3. For **some** torsion-free cocompact lattice `Λ <= L`, the action `A ↷ L/Λ` admits topological
   microstates. Equivalently, since the action is uniquely ergodic, the p.m.p. action
   `A ↷ (L/Λ, Haar)` is sofic.
4. The same holds for **every** torsion-free cocompact lattice `Λ <= L`.

Moreover, the twin deep models in item 2 can never be exact. That is part (b) of
`twin-deep-vertex-models-give-homogeneous-microstates`, which uses the normal subgroup theorem.

**Implications.** 2 ⇒ 4 is `twin-deep-vertex-models-give-homogeneous-microstates`. 4 ⇒ 1 is
`homogeneous-quotient-soficity-gives-vertex-soficity`, applied to a normal tower. 4 ⇒ 3 is trivial.
The new content is 1 ⇒ 2 and 3 ⇒ 2.
* **1 ⇒ 2 (charts become frames).** The injective chart labels of the type-zero vertices in a ball
  `B_R(v_0)` are a free torsor for the finite group `K/Fix(B_R)`. A fixed transversal (a *gauge*)
  turns them into an almost `C`-equivariant map to that group, and the adjacent ball gives the
  analogue for `C_1`.
* **3 ⇒ 2 (marks become cells).** Almost equivariant marks in `L/Λ` give almost equivariant maps to
  the finite regular sets of level-`R` cells.
* **Deep correction.** In both cases a correction lemma for `Z/2 * Z/3` acting over a regular finite
  set makes the actions exact and the maps exactly equivariant. It changes `O_R(ε)` points and pads
  by `O_R(ε)` points, so all stabilizers become `2`-adically deep.

**What it says.**
* **One problem, three faces.** Soficity of the countable vertex action, soficity of one compact
  uniquely ergodic algebraic system, and a finite modular-group construction are the *same*
  question. None of them is known.
* **Where negativity must live.** A proof that the vertex action is nonsofic is exactly a proof that
  the frame dynamics `PSL_2(Z[1/2]) ↷ PSL_2(Q_2)/Λ` admits no microstates, for one (hence every) `Λ`.
  By `psl2-bruhat-tits-action-soficity-forces-p-instability`, a positive answer on any face produces
  noncorrectable permutation models of `A`.
* **Forced structure of positive models.** Any positive model must contain the structure forced on
  twin models: non-congruence vertex orbits (`expanding-matchings-need-a-shared-stabilizer`),
  asymptotically free stabilizer laws, and no exact deep gluing.
* **Other lanes.** The GKP free wreath theorem gives `G_2 = <A,t | [t,C]>` sofic from any face
  (`sofic-dyadic-coset-action-makes-hnn-sofic`, stated there for `SL_2`; the action factors through
  `PSL_2`). A sofic frame dynamics also gives Cartan microstates of the crossed product in
  `sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`. That is a standard remark,
  not an edge here.

Proof in `dyadic-vertex-soficity-equals-frame-dynamics-soficity-proof`.
