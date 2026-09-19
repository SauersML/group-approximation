---
rg: 2
id: cp-failures-transfer-between-hyperbolic-and-leh-groups-proof
kind: route
title: Carry a finite partial-table witness through local embeddings and through one Olshanskii quotient of the host, a bad group and a finite-quotient-free group
target: cp-failures-transfer-between-hyperbolic-and-leh-groups
requires:
  - cover-pair-failures-have-finite-partial-table-witnesses
  - nonsofic-hyperbolic-question-reduces-to-one-fixed-host
  - olshanskii-g-subgroup-quotient-theorem
  - kapovich-wise-rf-iff-finite-quotients
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - hyperbolic-local-embedding-kills-compression-certificates
  - universal-all-group-subgroup-colimit-class-tester
  - whitehead-universal-finitely-presented-container
---

Write *Theorem L* and *Corollary n* for the parts of `cover-pair-failures-have-finite-partial-table-witnesses`.
Three facts about `P ∈ {CP, CP_col, NPE}` are used, and nothing else:
- **(i)** a failure at `G` has a finite witness set `K ∋ 1` and persists under partial embeddings of `K` (Theorem L);
- **(ii)** a failure at a subgroup is a failure at the group (Corollary 1);
- **(iii)** residually finite groups satisfy `P` (Corollary 5).

These are the three properties of soficity that the route of `nonsofic-hyperbolic-question-reduces-to-one-fixed-host`
uses. The steps below repeat that route with (i)–(iii) in place of its table closedness.

**(1) ⇒ (2).** A hyperbolic group is LEH, taking the inclusion as the partial embedding.

**(2) ⇒ (1).** Let `K_0` be LEH, fail `P`, and have witness set `K`. By definition of LEH, `K` has a partial
embedding into some hyperbolic `H`. By (i), `P` fails at `H`.

**(3) ⇒ (4)** is the case `M = ∅`, and **(4) ⇒ (1)** is immediate.

**(1) ⇒ (3).** Let `G` be hyperbolic, failing `P`, with finite witness set `K ⊆ G`. (A hyperbolic
group is finitely generated, and no ball is needed below, only `K`.)
- *A finite-quotient-free partner.*
  - `G` is not residually finite, by (iii).
  - By `kapovich-wise-rf-iff-finite-quotients` (contrapositive form), some infinite hyperbolic `G_0` has no
    nontrivial finite quotient.
  - Put `G_1 = G_0 / E(G_0)`. As in the route of `nonsofic-hyperbolic-question-reduces-to-one-fixed-host`, `G_1`
    is non-elementary hyperbolic, finite-quotient-free, and has `E(G_1) = 1`.
- *The amalgam.* Let `L = G * T * G_1`, a non-elementary hyperbolic group. The *Finite radicals* paragraph of that
  route shows `E(L) = E_L(T) = E_L(G_1) = 1`, using only `E(T) = E(G_1) = 1` and Kurosh. So, by clause 1 of
  `olshanskii-g-subgroup-quotient-theorem`, `T` and `G_1` are G-subgroups of `L`.
- *The quotient.* Let `M ⊆ T` be finite and `M' = M ∪ K ∪ {1}`. Clause 2 of `olshanskii-g-subgroup-quotient-theorem`
  gives an epimorphism `φ : L → Q` onto a non-elementary hyperbolic group, injective on `M'`, with
  `φ(T) = φ(G_1) = Q`. Put `π = φ|_T`. It is onto and injective on `M`.
  - *`Q` fails `P`.* `φ|_K : K → Q` is injective, and multiplicative because `φ` is a homomorphism. So it is a
    partial embedding of `K`, and by (i) `P` fails at `Q`.
  - *No finite quotients.* A finite quotient of `Q` pulls back along the surjection `φ|_{G_1}` to a finite quotient
    of `G_1`, so it is trivial. ∎

Compared with the soficity route, the ball `B_R(G)` and the transfer of equalities of words are replaced by the
single set `K`. This is because Theorem L asks only for a partial embedding of `K`, and the restriction of a
homomorphism that is injective on `K` is one.

**Kazhdan host.**
- A torsion-free infinite group has trivial finite radical, so (3) applies to the group `T` of
  `torsion-free-hyperbolic-kazhdan-partner-exists`.
- A quotient of a Kazhdan group is Kazhdan, so every `Q` in (3) is Kazhdan.
- The statement about CP at LEH groups is (1) ⇔ (2) ⇔ (4) with `P = CP`.

**Obstruction at the tester.**
- *`P(all) ⇔ P(U)`.* This is Corollary 4.
- *`U` is not LEH.*
  - Thompson's group `F` is finitely presented, hence recursively presented. So it embeds in `U` by
    `whitehead-universal-finitely-presented-container`, which is the host fixed in
    `universal-all-group-subgroup-colimit-class-tester`.
  - By Consequence 1 of `hyperbolic-local-embedding-kills-compression-certificates`, no LEH group contains `F`.
  - Finite groups are hyperbolic, so LEF groups are LEH. Residually finite groups are LEF. So `U` is neither LEF
    nor residually finite.
- *Model transfer reaches all groups iff `U` is locally embeddable into `C`.*
  - (⇐) Every finitely presented group is a subgroup of `U`, and local embeddability into `C` passes to subgroups.
  - Every group `G` is locally embeddable into finitely presented groups. For finite `K ⊆ G`, take the
    presentation with generators `K` and relators `ab = c` for all `a, b, c ∈ K` with `ab = c` in `G`. The
    evident map sends `K` injectively and multiplicatively into it, because the presented group maps onto `⟨K⟩`
    compatibly.
  - Partial embeddings compose. For the second one, embed the image of `K` together with the finitely many
    products used. So `G` is locally embeddable into `C`.
  - (⇒) is trivial.
  - The classes of finite, residually finite, LEF, hyperbolic and LEH groups are all contained in LEH, which is
    closed under local embeddability. So `U` lies outside every one of them.
- *The universal sentence of the remark* is illustrative and is not used above. ∎
