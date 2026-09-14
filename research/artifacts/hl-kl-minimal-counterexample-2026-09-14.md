# Minimal Kervaire--Laudenbach counterexamples: simple acyclic and finitely presented acyclic normal forms

Lane hl-kl-minimal-counterexample, 2026-09-14. Landed unreviewed.

Conventions: `G_w = (G * <t>)/<<w>>` for `w in G * <t>` with `deg_t(w) = m != 0`.
A *failure* is a triple `(G, w, a)` with `1 != a in G` dying in `G_w`.
"Acyclic" means `H_n(G; Z) = 0` for every `n >= 1`.

## 1. Sources read this session (verbatim)

**Palmer--Wu**, *Embedding groups into acyclic groups*, arXiv:2510.16879v1
(dated 19 Oct 2025), read from the arXiv PDF:

- Introduction: "Recall that a (discrete) group G is called *acyclic* if it has
  the homology of a point."
- **Theorem C (Theorem 2.22).** "For any group G acting faithfully on a
  countable set S, the associated twisted Brin–Thompson group SV_G is acyclic."
- "The key property of the groups SV_G is that they are always simple [BZ22,
  Theorem 3.4]."
- "Combining Theorem C with [BZ22, Theorems A, B, 3.4] and taking S = G with the
  regular G-action, we have the following."
- **Corollary 0.10.** "Every finitely generated group embeds quasi-isometrically
  into a 2-generated, simple, acyclic group."
- **Theorem A (Theorem 2.6).** "For any discrete group G, the labelled Thompson
  group V(G) is acyclic."
- **Theorem ([Tho80, WWZZ25]).** "The functor V and the embedding ι_0 have the
  following properties, for any discrete group G: (1) ι_0: G ↪ V(G) is
  injective, and is also a quasi-isometric embedding when G is finitely
  generated; (2) ι_0: G ↪ V(G) is Frattini; (3) V(G) has solvable word problem
  if and only if G has solvable word problem; (4) V(G) is of type F_n if and
  only if G is of type F_n; (5) V(G) has no proper finite-index subgroups; (6)
  V(G) is 5-uniformly perfect; (7) V(G) is boundedly acyclic."
- **Proposition B.** "For any discrete group G, we have: the centre of V(G) is
  isomorphic to the centre of G; the group V(G) is strongly torsion generated."
- **Corollary 0.2.** "Any group of type F_n embeds quasi-isometrically as a
  subgroup of an acyclic group of type F_n that has no proper finite-index
  subgroups."
- **Corollary 0.4.** "There is a finitely presented, strongly torsion generated,
  acyclic group with no proper finite-index subgroups into which every
  recursively presented group embeds."
- Background, as Palmer--Wu report it (originals NOT read here): "Baumslag–
  Dyer–Heller, who proved in [BDH80] that every finitely generated group (and
  hence every countable group by [HNN49, Theorem IV]) embeds into a finitely
  generated acyclic group"; "Baumslag–Dyer–Miller [BDM83], who showed that
  every finitely presented group embeds into a finitely presented acyclic
  group".
- Bibliography, verbatim:
  - [BZ22] James Belk and Matthew C. B. Zaremsky. Twisted Brin-Thompson groups.
    Geom. Topol., 26(3):1189–1223, 2022.
  - [BDH80] G. Baumslag, E. Dyer, and A. Heller. The topology of discrete
    groups. J. Pure Appl. Algebra, 16(1):1–47, 1980.
  - [BDM83] G. Baumslag, E. Dyer, and C. F. Miller, III. On the integral
    homology of finitely presented groups. Topology, 22(1):27–46, 1983.
  - [Tho80] Richard J. Thompson. Embeddings into finitely generated simple
    groups which preserve the word problem. Word problems, II, Stud. Logic
    Found. Math. 95, 401–441, 1980.
  - [WWZZ25] Fan Wu, Xiaolei Wu, Mengfei Zhao, and Zixiang Zhou. Embedding
    groups into boundedly acyclic groups. J. Lond. Math. Soc. (2), 111(5),
    e70164, 2025.

**Fournier-Facio--Löh--Moraschini**, *Bounded cohomology and binate groups*,
arXiv:2111.04305v3: "Definition 1.2. A group Γ is said to be acyclic if
H_n(Γ;Z) ≅ 0 for all n ≥ 1." Also: binate groups "were introduced by Berrick
[4] and independently by Varadarajan [55] ... They proved that binate groups
are acyclic".

Status of the import: a reading of a 2025 arXiv preprint, not a refereeing.
Corollary 0.10 rests on Theorem C, which uses Xin Li's homology theorem for
ample groupoids ([Li25], Forum Math. Pi 2025), and on [BZ22, Theorems A, B,
3.4]. None of those inputs was re-derived here.

## 2. The overgroup transfer (used everywhere below)

**Lemma T.** If `(A, w, a)` is a failure and `A <= H`, then `(H, w, a)` is a
failure.

*Proof.* The inclusion `A * <t> -> H * <t>` is injective and maps
`<<w>>_(A*<t>)` into `<<w>>_(H*<t>)`. So `a` lies in the latter, and `a != 1`
in `H`. ∎

This is Attempt 2 of `kl-counterexample-can-be-superperfect-quasisimple`,
restated.

## 3. Theorem 1: a two-generator simple acyclic counterexample

**Theorem 1.** If the nonsingular Kervaire--Laudenbach conjecture fails at
degree `m`, then it fails at degree `m` over a two-generated infinite simple
acyclic group `S`. For that failure, `S_w = C_|m|`. For any prescribed
countable group `C`, `S` can be chosen to contain a copy of `C`.

*Proof.*
1. `kl-failure-localizes-to-the-coefficient-subgroup` (established) turns a
   failure `(G, w, a)` into a failure `(A, w, a)` with `A` finitely generated.
2. Given `C`, embed it in a two-generator group `C'`. Use
   `countable-group-embeds-in-two-generator-simple-group` (established in the
   graph), or HNN49 Theorem IV as reported above. Put `B = A * C'`, which is
   finitely generated and contains `A`.
3. Palmer--Wu Corollary 0.10 gives `B <= S` with `S` 2-generated, simple and
   acyclic. Lemma T makes `(S, w, a)` a failure.
4. **`S` is infinite.** Finite groups are hyperlinear, so they satisfy the
   conjecture by `kervaire-laudenbach-holds-for-hyperlinear`. `S` does not
   satisfy it, so `S` is infinite, hence nonabelian: abelian simple groups are
   cyclic of prime order.
5. **The cyclic quotient.** `kl-simple-failure-leaves-only-the-cyclic-quotient`
   gives `S_w = C_|m|` and `<<w>>_(S*<t>) = N_m`. ∎

**Corollary 1 (decides `kl-counterexample-can-be-superperfect-quasisimple`).**
The group `S` of Theorem 1 is two-generated, `H_1(S) = H_2(S) = 0`, and
`Z(S) = 1`, so `S/Z(S) = S` is nonabelian simple. It is therefore a
two-generator superperfect quasisimple counterexample, with trivial centre.

Remarks:
- For `S` acyclic, `H_2(S) = 0`, so the universal central extension is `S`
  itself. Item 3 of
  `kl-simple-failure-universal-cover-collapses-when-centralized` asks whether
  some simple failure lifts to the collapsing case; this one does, trivially.
  Whether EVERY simple failure lifts stays open and is not needed.
- **A route independent of Palmer--Wu.** Embed `A` in a countable acyclic group
  `B` (BDH80, secondary reading only). Embed `B` in a two-generator simple `S`
  (Schupp). Every central extension of `B` splits, since
  `H^2(B; M) = Hom(H_2 B, M) ⊕ Ext(H_1 B, M) = 0`. So `B` lifts into the
  universal central extension `S^`, which is two-generated, superperfect and
  quasisimple (graph, item 1 of the node above). Lemma T puts the failure on
  `S^`. That gives the original claim with centre `H_2(S)`. It is recorded as a
  robustness remark only: BDH80 and Schupp were not read at source.

## 4. Theorem 2: finitely presented acyclic, and one fixed group

**Theorem 2.**
- **(a)** If the conjecture fails at degree `m`, it fails at degree `m` over a
  finitely presented acyclic group `Q` that has no proper finite-index
  subgroups, is strongly torsion generated, and has solvable word problem
  whenever the finitely presented counterexample it contains does.
- **(b)** Let `U_ac` be the group of Palmer--Wu Corollary 0.4. The nonsingular
  conjecture holds for all groups if and only if it holds over `U_ac`.

*Proof.*
- **(a)** `kl-counterexample-can-be-finitely-presented` (established) gives a
  failure `(P, w, a)` with `P` finitely presented. Put `Q = V(P)`:
  - `ι_0` embeds `P` in `Q` (item 1);
  - `Q` is finitely presented because a group is of type `F_2` iff it is
    finitely presented (item 4);
  - `Q` is acyclic (Theorem A);
  - `Q` has no proper finite-index subgroups (item 5);
  - `Q` is strongly torsion generated (Proposition B);
  - the word problem is preserved (item 3).
  Lemma T finishes. ∎
- **(b)** A finitely presented `P` is recursively presented, so it embeds in
  `U_ac`, and Lemma T applies. The other direction is trivial. ∎

What (b) does not give: `U_ac` has unsolvable word problem, since it contains
every recursively presented group. So the single-group form fixes the host but
not decidability. Higman's universal finitely presented group gives the same
equivalence without acyclicity.

## 5. Remark: the unimodular killing form is a contractible complex

For a nontrivial group `G` and `w in G * <t>` with `deg_t(w) = ±1`, put
`Y = K(G,1) ∨ S^1` and `X = Y ∪_w e^2`.
- van Kampen gives `pi_1(X) = G_w`.
- `H_n(Y) = H_n(G) ⊕ H_n(S^1)` for `n >= 1`. The attaching map sends the
  2-cell's boundary to `([w]_G, ±1)` in `H_1(Y)`, which is injective.
- So `H_1(X) = H_1(G)`, `H_2(X) = H_2(G)`, and `H_n(X) = H_n(G)` for
  `n >= 3`.

Hence `X` is contractible iff `G_w = 1` and `G` is acyclic: a simply connected
CW complex with vanishing reduced homology is contractible, by Hurewicz and
Whitehead. With Theorem 1 at `m = ±1`, the classical conjecture fails iff some
`X` of this shape is contractible with `G != 1`. Likely folklore; no novelty is
claimed.

For infinite `G`, `b_1^(2)(G * Z) = b_1^(2)(G) + 1 >= 1`. So the aspherical
one-cell complement `Y` of the contractible `X` has positive first
L²-Betti number. This is no Whitehead counterexample, since `Y` is aspherical.
It only shows that the finite-complex hypothesis in
`one-cell-complement-groups-have-vanishing-first-l2-betti` is essential.

## 6. Exact gaps and what does not follow

- **Finitely presented and simple at once:** still
  `kl-counterexample-can-be-finitely-presented-simple` (OPEN, needs
  Boone--Higman for one group).
  - Palmer--Wu Corollary 0.10 envelopes are the twisted Brin--Thompson groups
    `SV_G` for the regular action. [BZ22] finiteness needs finitely many orbits
    on finite subsets, which the regular action of an infinite group lacks, so
    no finitely presented simple envelope follows.
- **Solvable word problem:** `kl-counterexample-can-have-solvable-word-problem`
  stays OPEN. Theorem 2(a) transports decidability but does not create it.
- **Non-hyperlinear endpoint.** A counterexample yields:
  - a 2-generated simple acyclic non-hyperlinear group;
  - a finitely presented acyclic non-hyperlinear group with no proper
    finite-index subgroups.

  This adds nothing to the existence of a non-hyperlinear group. Palmer--Wu
  embed ANY finitely generated non-hyperlinear group into such envelopes. The
  new content is only that the counterexample can be taken in these normal
  forms.
- **Finite search.** A failure over a fixed finitely presented group with
  solvable word problem has an r.e. certificate. No single finitely generated
  host with solvable word problem contains all such groups (Boone--Rogers, not
  re-read), and `U_ac` is undecidable. So the normal forms do not reduce the
  conjecture to a finite search.
