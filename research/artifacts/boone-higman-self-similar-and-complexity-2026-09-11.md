# Boone--Higman: self-similar hosts and the complexity necessity

Lane `boone-higman-2`, 2026-09-11. Scope split with lane `boone-higman`:
this lane takes the shell/germ and twisted Brin--Thompson envelopes built
directly for decidable inputs, the Leavitt ring host and the infinite-simple
input form. The other lane keeps the Chatterji--Kassabov maximal kernel, the
finite bi-index envelope, the fiber-product data, and FFWZ Lemma 5.5 /
Question 5.9.

## 1. Sources read

**Belk--Bleak--Matucci--Zaremsky, *Progress around the Boone--Higman
conjecture*** (Glasgow eprint 359114, read from the PDF pages 1--24).

* Theorem 4.15 (Zaremsky 2025): a faithful action of a finitely presented
  group with finitely generated point stabilizers and finitely many orbits
  of pairs embeds the group in the finitely presented simple group `SV_G`.
* Corollary 4.16: every contracting self-similar group embeds in a finitely
  presented simple group.
* Theorem 5.1(12): "Contracting self-similar groups and finitely presented
  self-similar groups."
* Problem 5.3, verbatim items: "(1) Braid groups. (2) Mapping class groups of
  surfaces. (3) The groups Aut(F_n) and Out(F_n). (4) Non-solvable
  Baumslag--Solitar groups BS(m,n) ... (5) GL_n(Q). (6) Free Burnside groups
  B(m,n) with solvable word problem. (7) Finitely presented metabelian
  groups. (8) Free-by-cyclic groups. (9) One-relator groups (without torsion).
  (10) CAT(0) groups. (11) Automatic groups. (12) Finitely presented
  residually finite groups. (13) Artin groups with solvable word problem."
* Remark 5.4: Bux--Llosa Isenrich--Wu (arXiv:2408.05673) settle (4) and (8);
  Belk--Fournier-Facio--Hyde--Zaremsky settle Aut(F_n), hence (1) and parts
  of (2), (3), (13). Item (12) is not reported settled.
* Section 4.4: "we are unaware of any examples of finitely generated groups
  with solvable word problem that do not embed into a finitely presented
  twisted Brin--Thompson group", and the family is universal among finitely
  presented simple groups with faithful highly transitive actions [BFFHZ].

**Zaremsky, arXiv:2405.09722** (v2 HTML; BLMS 2025, doi:10.1112/blms.70022).

* Definition: "A subgroup G <= Aut(T_d) is self-similar if its image in
  S_d wr_d Aut(T_d) under the above isomorphism is contained in S_d wr_d G."
* Theorem 1.1: "Every finitely presented self-similar group embeds in a
  finitely presented simple group, and hence satisfies the Boone--Higman
  conjecture."
* Theorem 1.2: "Every finitely generated subgroup of GL_n(Q) satisfies the
  Boone--Higman conjecture." The abstract says the simple groups are
  commutator subgroups of Rover--Nekrashevych groups.

No primary source was found stating finitely presented simple groups with
arbitrarily complex word problem; the only search statements seen describe
that as open and as a consequence of Boone--Higman. The graph does not cite
those search results; the implication is proved directly below.

## 2. Nodes landed

* `fp-self-similar-groups-embed-in-fp-simple-groups` (citation import).
* `fp-residually-finite-groups-have-solvable-word-problem` (classical, proved).
* `fp-residually-finite-boone-higman`, root, OPEN: Problem 5.3(12).
  Routes: from the conjecture, and via
  `every-fp-rf-group-embeds-in-fp-self-similar-group` (OPEN).
* `graph-shift-groups-have-arbitrarily-hard-word-problem` (proved).
* `complexity-bounded-host-classes-are-not-universal` (proved).
* `fp-simple-groups-with-arbitrarily-complex-word-problem`, root, OPEN,
  implied by the conjecture through `complex-fp-simple-groups-from-boone-higman`.

The proofs are in the route files. The hardness construction uses
`G_A = A(Gamma_A) x| Z`, where `Gamma_A` joins `i` and `j` when `|i-j| in A`.
The word `[a, b^-n a b^n]` is trivial iff `n in A`, by retraction onto the
two-vertex subgraph, and the clocked diagonalization over (machine, constant)
pairs makes `A` decidable but beyond every bound of the form
`C*T(C*l)+C*l+C`.

## 3. Why the complexity node matters for this lane

Every universal envelope must produce hosts with unboundedly complex word
problem. So the construction has to consume the input's algorithm, and the
finiteness that makes the host finitely presented cannot come from a bounded
amount of local dynamics (finitely many cone types, contraction, finite
state). The existing rational and automaton screens are special cases.
Candidates that survive it by design: shift and shell envelopes whose
enumeration encodes the input, twisted Brin--Thompson groups over complex
actors, and finitely presented self-similar groups with infinitely many
states.

## 4. Shell route: two observations recorded here, not as nodes

**(a) The shift germ comes from the base point.** In
`shell-cantor-embeddings-are-finite-germ-extensions` the base point is
`p = 0^infinity`, and the isotropy germ group is `<rho(P), tau>`. At a base
point that is not eventually periodic the V-isotropy germ is trivial: if a
prefix replacement `u -> u'` fixes `p` with `|u'| != |u|`, the tail of `p` is
periodic. Putting the regular action of `P` on all shells around such a point
gives isotropy germ group exactly `P`, so the necessary finite-presentation
test on the germ group is automatic. The price is that the V-stabilizer of the
point is the directed union `union_n Fix_V(p_[0,n) C)`, which is not finitely
generated. The one-point stabilizer becomes `K x| P`, with `K` the locally-V
group on the `P`-indexed shells. It is finitely generated, because the shell
pairs `{1, s}` for generators `s` form a connected orbit graph, but it looks
like a permutational Thompson wreath and is not expected to be finitely
presented. No proof either way, so nothing is noded. This suggests that the
contracting shift is what makes point stabilizers ascending HNN extensions,
as for `V_p`. The germ obstruction is then the price of finite presentation,
not an artifact.

**(b) A nonrational two-dimensional positive control may exist.** For
`P = Z^2` with the square-spiral enumeration, the successor is a piecewise
translation on four cones separated by the diagonals. The generators
`T_(1,0), T_(0,1)` and the successor then share an abelian "germ at infinity"
invariant, a piecewise constant translation vector on directions. Commutators
are supported near the four diagonal rays, where the spiral pattern is
periodic along each ray. Heuristically the near group is Houghton-like on four
decorated rays, and its index-zero kernel is generated by boundedly many
shifts. If that were proved, `R_nu` would be finitely presented with finitely
generated kernel, and the germ group finitely presented by the 1-2-3 theorem.
That would be the first non-virtually-cyclic enumeration passing the germ
test, while staying compatible with
`rational-regular-shell-actions-require-virtually-cyclic-input`, since the
spiral action is not rational. Not attempted in full here.

## 5. The Leavitt container, after Khanh

Lane `lit-groups` imported Khanh, arXiv:2609.08428v1, Theorem 6.1: `R^x` is
finitely presented for `R = L_(F_2)(1,2)`. That is claim
`leavitt-unit-group-finitely-presented`, unreviewed preprint. With
`binary-leavitt-unit-group-is-simple`, `R^x` is a finitely presented simple
container. Landed consequences:

* `leavitt-subalgebra-linear-groups-satisfy-boone-higman` (f2b36666c): an
  `n`-leaf complete prefix code gives a unital isomorphism `M_n(R) ≅ R`, so
  `GL_n(A) <= R^x` for every unital subalgebra `A <= R`.
* `char-two-laurent-linear-groups-satisfy-boone-higman` (f2b36666c): prefix
  monomials give the free algebras; the Thompson unit
  `g = s_0 t_0 t_0 + s_1 s_0 t_1 t_0 + s_1 s_1 t_1` (inverse
  `s_0 s_0 t_0 + s_0 s_1 t_0 t_1 + s_1 t_1 t_1`, checked by expansion) gives
  `F_2[g,g^-1]`, since its powers move the basis vector `10000...` of the
  eventually-zero test module to distinct basis vectors.
* `char-two-curve-linear-groups-satisfy-boone-higman` (22cb987f5): every
  finitely generated linear group over a characteristic-two field of
  transcendence degree at most one. `F_2[t,1/f] ≅ F_2[g^±][T]/(f(T)-g)` is
  free of rank `deg f` over `F_2[g^±]`, so it sits in `M_d(F_2[g^±])`.

The container is one fixed group, so by the complexity wall it is not
universal. It supplies a positive-characteristic family that is not in the
BBMZ survey's list, where the only linear results are `GL_n(Z)` and
Zaremsky's `GL_n(Q)`.

## 6. A reduction worth recording later (not noded yet)

`B ⊗ L_(F_2)(1,2)` contains `GL_n(B)` through the same prefix codes. So
Boone--Higman would follow from two algebra statements: (i) every finitely
generated `F_2`-algebra with solvable word problem, in particular every group
algebra `F_2[H]` of a decidable group, embeds unitally in a finitely presented
simple `F_2`-algebra `B`; (ii) for such `B`, the unit group of `B ⊗ L` modulo
its centre is finitely presented and simple (Khanh's theorem is the case
`B = F_2`). Evans--Mandelberg--Neff (Logic Colloquium '73) prove
"Boone--Higman type theorems" for rings of characteristic p. Their exact
statement could not be read (403), so whether (i) is known was not verified.

## 7. Next steps for this lane

1. Decide (b) for `Z^2`. This is a finite amount of piecewise-translation
   combinatorics and settles whether the shell germ gate is passable beyond
   virtually cyclic inputs.
2. For `every-fp-rf-group-embeds-in-fp-self-similar-group`, look for a
   finitely presented residually finite group that is residually `W_d` for no
   `d`. That would refute the claim and kill the self-similar route.
3. Neighbour input (lane `boone-higman`, commit 92437e028): Boone--Higman
   implies a finitely presented simple group with full MF radical, so every
   universal envelope must contain such groups. A family of envelopes proved
   MF, or proved to admit nontrivial finite-dimensional representations, is
   non-universal.
