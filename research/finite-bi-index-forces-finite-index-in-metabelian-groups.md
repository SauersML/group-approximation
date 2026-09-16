---
rg: 2
id: finite-bi-index-forces-finite-index-in-metabelian-groups
kind: claim
title: In virtually polycyclic groups and finitely generated abelian-by-virtually-abelian groups every subgroup with finitely many double cosets has finite index
distinct_from:
  type-a-actors-have-no-infinite-virtually-central-subgroup: that forbids an infinite virtually central subgroup in a faithful actor with finitely many orbits on two-element subsets; this shows that every transitive finite-rank action of a virtually polycyclic or abelian-by-virtually-abelian group is finite, with no faithfulness hypothesis, including groups with trivial centre.
  fp-simple-type-a-actions-iff-finite-bi-index-subgroups: that characterises type (A) actions of finitely presented simple groups through finite bi-index subgroups; this shows that in the stated solvable classes a finite bi-index subgroup is just a finite-index subgroup.
  finite-bi-index-subgroups-have-decidable-membership: that decides membership in a finitely generated finite bi-index subgroup of a group with solvable word problem; this proves that such subgroups have finite index when the ambient is virtually polycyclic or abelian-by-virtually-abelian.
artifacts:
  - research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md
---

ESTABLISHED by `finite-bi-index-metabelian-proof`. **Not new.** Both cases are
special cases of Y. de Cornulier, *Finitely presented wreath products and
double coset decompositions*, arXiv:math/0509090v2 (revised 2006-12-02),
Proposition 3.20: a finitely generated nilpotent-by-(virtually polycyclic) group
has Property (MF). By his Lemma 3.2 a subgroup of finite bi-index is almost
maximal, so (MF) implies Property (BF): every subgroup of finite bi-index has
finite index. Cornulier's proof uses Roseblade's theorem that simple modules
over virtually polycyclic group rings are finite (his Theorem 3.21). (Referee
check of the arXiv PDF, 2026-09-16.) The route here is a self-contained
elementary proof of the special case stated below. It avoids Roseblade's
theorem because the orbit modules that occur are modules over virtually abelian
groups.

## Statement

A `K`-set `Y` has **finite rank** if `K` has finitely many orbits on `Y x Y`. For
`Y = K/C` the rank is the bi-index `|C\K/C|`.

**Theorem.** Let `Y` be a transitive `K`-set of finite rank. Then `Y` is finite
if either:

- (i) `K` is virtually polycyclic; or
- (ii) `K` is finitely generated and has an abelian normal subgroup `A` with
  `K/A` virtually abelian. This includes every finitely generated metabelian
  group.

Equivalently, in these groups every subgroup `C` with `|C\K/C| < infinity`
satisfies `|K : C| < infinity`.

**Lemma (fields).** A field whose multiplicative group is finitely generated is
finite.

## Consequence for commuting-conjugate switches

Let `e -> (K_e, S_(C_e), U_e)` be computable, with finite presentations `K_e` and
finite word sets `S_(C_e)`, `U_e`. Put `D_e = C_e cup C_e U_e C_e cup C_e U_e^-1 C_e`.

Suppose every `K_e` with `K_e = D_e` is virtually polycyclic, or abelian-by-virtually-abelian.
Then `{e : K_e = D_e}` is `Sigma^0_1`. A certificate is a finite transitive
action satisfying the relators whose base point is fixed by `S_(C_e)`, with
derivations placing the Schreier generators of the stabilizer in `C_e`, and whose
point set is covered by the `C_e`-orbits of the points `y_0`, `u y_0` and
`u^-1 y_0`.

So by `commuting-conjugate-switch-amenability-criterion`, a `Pi^0_2`-hardness
reduction through that switch cannot use such ambients. It needs a finitely
presented amenable `K` with a subgroup of infinite index and finite bi-index.
Houghton groups `H_n` (`n >= 3`) are elementary amenable examples of rank two,
which shows that (ii) does not extend to all elementary amenable groups
(Cornulier, loc. cit., Example 3.6). The solvable class-three case, including the
KMS machine groups in `A_p^2 A`, is Cornulier's Question 3.24(1). By his
Proposition 3.23 with `n = 3`, it is equivalent to asking whether some finitely
generated metabelian group has an infinite module with finitely many orbits.
It is recorded there as open (v2, 2006). Its later status was not rechecked here.
See the artifact, Section 5.
