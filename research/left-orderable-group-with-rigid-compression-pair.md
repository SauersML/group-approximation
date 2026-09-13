---
rg: 2
id: left-orderable-group-with-rigid-compression-pair
kind: claim
title: Some left-orderable group contains an infranormal non-normal Kazhdan pair
distinct_from:
  hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup: that exhibits a rigid pair inside a word-hyperbolic group with no order structure; this asks for a rigid pair inside a left-orderable group, which is what the order question needs.
  kt-pair-group-double-is-nonsofic: that is the nonsoficity conclusion for the double of any rigid pair; this is the existence of a rigid pair in the one ambient class where the known pairs are unavailable.
---

**Statement (OPEN).**  There are groups `Gamma <= G` such that

- `G` is left-orderable;
- `Gamma` and `G` have Kazhdan's property (T);
- `Gamma` is infranormal in `G`, that is
  `P_Gamma = {g in G : g Gamma g^-1 <= Gamma}` generates `G`;
- `Gamma` is not normal in `G`.

Left-orderability is subgroup-closed, so asking for a left-orderable ambient
group containing the pair is the same as asking that `G` be left-orderable.

**Why it matters.**  It is exactly the input of
`left-orderable-non-sofic-via-integer-lamp-rigid-pair`, which turns such a
pair into a left-orderable nonsofic group.

**What it costs.**  A finite infranormal subgroup is normal
(`finite-infranormal-subgroup-is-normal`), so `Gamma` is infinite.  Hence this
claim implies `infinite-left-orderable-kazhdan-group`, which is Navas's
Question 3 (arXiv:1712.06462v2), open.  So this claim is at least as hard as
a positive answer to that question.

**Model test.**  Trivial models fail it: `Gamma = G` is normal, and a finite
`Gamma` is normal.  The Theorem E pair
(`Gamma = EL_r(F_q[x_1..x_d])`, `G = EL_r(F_q[x^(+-1)]) x| SL_d(Z)`) satisfies
every clause except left-orderability, since its elementary matrices have
order `p`.

## Attempts

**The known rigid pairs.**  Each one dies on torsion or behind Navas's question.

- The Theorem E pair and the OpenAI nine-leaf Leavitt pair contain torsion:
  elementary matrices over `F_q`, and Thompson's `V`.  Neither is
  left-orderable.
- The hyperbolic Leavitt cover
  (`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`) and the
  Fournier--Facio pair (`fournier-facio-torsion-free-skeleton`) are rigid pairs
  whose orderability is unknown.  Proving either left-orderable would answer
  Navas's Question 3 positively.  For the Fournier--Facio group one cannot
  shortcut through a non-orderable subgroup: its source group `P` contains a
  universal torsion-free group, but the quotient map is known to be injective
  only on a finite ball and on `S` (`fournier-facio-group-hyperlinear`,
  "No universality").

**Locally indicable or bi-orderable ambient groups.**  Dead.  Every nontrivial
finitely generated subgroup of a locally indicable group maps onto `Z`, and a
Kazhdan group has no infinite abelian quotient.  So a locally indicable group
contains no nontrivial Kazhdan subgroup.  Bi-orderable groups are locally
indicable.  The same argument closes one-relator hosts
(`torsion-free-one-relator-has-no-kazhdan-subgroup`).

**The compression shape is never the obstruction in ordered groups.**  Take
Thompson's group `F` acting on the line as dyadic PL homeomorphisms.  Let
`Gamma` be the copy supported in `(0,1)` and `J` the copy supported in `(1,2)`.
Let `t` be a dyadic PL homeomorphism with `t((0,2)) = (0,1)`.  Then
`t Gamma t^-1 <= Gamma`, `[Gamma, J] = 1`, `Gamma cap J = 1`,
`t J t^-1 <= Gamma`, and `J ~= F` is not LEF.  This is the full OpenAI
compression shape, inside a bi-orderable group.  What is missing is the
rigidity of `Gamma`.

**Replace (T) by relative property (T) of an amenable subgroup.**  Dead for
both Kun--Thom outputs whenever `G` is sofic.  Relatively Kazhdan pairs do
occur in ordered groups: `F_2 x| Z^2` has relative (T) with respect to `Z^2`
and embeds in the group of orientation-preserving homeomorphisms of the
interval (Navas, arXiv:1712.06462v2, p. 3).  But if the infranormal `Gamma`
is amenable, every point stabilizer `g Gamma g^-1` of `G -> G/Gamma` is
amenable.  So the coset action of a sofic `G` is sofic (Alekseev--Bradford,
arXiv:2601.18742, Theorem 4.18, transcribed verbatim in
`research/artifacts/kun-thom-2608-06222-verified.md`), and every lamp wreath
`A wr_(G/Gamma) G` with sofic `A` is sofic (Gao--Kunnawalkam Elayavalli--Patchell,
arXiv:2401.04945, Theorem A, same artifact).  The rigid subgroup has to be
nonamenable, and the only known source of the expander decompositions the
mechanism consumes is property (T) itself.
