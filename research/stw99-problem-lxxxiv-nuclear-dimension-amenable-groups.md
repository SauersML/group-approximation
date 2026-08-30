---
rg: 2
id: stw99-problem-lxxxiv-nuclear-dimension-amenable-groups
kind: claim
title: Determine which amenable groups have group C*-algebras of finite nuclear dimension (STW Problem LXXXIV)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw84-local-rank-and-locally-finite-factor-audit-2026-08-30.md
  - research/artifacts/stw84-almost-free-permutation-wreath-2026-08-30.md
  - research/artifacts/stw84-common-stabilizer-wreath-2026-08-30.md
  - research/artifacts/stw84-commensurable-stabilizer-wreath-2026-08-30.md
  - research/artifacts/stw84-finite-stabilizer-menu-wreath-2026-08-30.md
  - research/artifacts/stw84-abelian-by-local-virnil-audit-2026-08-30.md
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

**Problem LXXXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Determine for which countable discrete amenable
groups the group C\*-algebra has finite nuclear dimension; better, compute it.

Known: polynomial growth gives finite decomposition rank (Eckhardt--Gillaspy--
McKenney); finitely generated virtually polycyclic groups have finite nuclear
dimension bounded by the Hirsch length (Eckhardt--Wu, STW Theorem 40);
`C*(ℤ≀ℤ)` has infinite nuclear dimension (from Giol--Kerr), while the
lamplighter `(ℤ/2)≀ℤ` has finite nuclear dimension but not finite
decomposition rank (it is not strongly quasidiagonal).  Eckhardt--Wu
conjecture: finite nuclear dimension iff finite Hirsch length.

## New reductions and exact classes

The exact finitely generated virtually abelian computation now has a twisted
counterpart.  Glebe--Karmakar--Moutzouris, arXiv:2605.27936v1, Theorem 4.12,
prove that for every rational cocycle class `[sigma]` on such a group `G`,

```text
dim_nuc C*(G,sigma)=h(G).
```

The imported claim `gkm-rational-twists-have-hirsch-nuclear-dimension`
retains finite generation, virtual abelianness, and rationality exactly.  It
does not classify irrational twists or enlarge the class of underlying
amenable groups in the untwisted STW problem.

The lower-bound theorem `stw84-abelianization-rank-lower-bound` shows that
finite nuclear dimension forces the abelianization to have finite rational
rank.  This gives an immediate infinite-dimensional certificate for every
amenable group surjecting onto an infinite-rank abelian group.

There is now a nonabelian quotient obstruction which can remain effective
when that rank is zero.  `stw84-wreath-quotient-obstruction` proves that every
countable amenable group surjecting onto `K wr H` has infinite-dimensional
group C*-algebra whenever `K` is infinite virtually polycyclic and `H` is
infinite finitely generated virtually nilpotent.  In particular
`D_infinity wr D_infinity` has finite abelianization but infinite nuclear
dimension, and the same conclusion holds for all its countable amenable
extensions.

The inductive-limit theorem `stw84-directed-union-uniform-bound` passes a
uniform nuclear-dimension bound from an increasing exhaustion by amenable
subgroups to the whole group.  Combined with the exact finitely generated
virtually abelian calculation, it proves
`stw84-locally-virtually-abelian-uniform-rank`: a countable locally virtually
abelian group of finite uniform local Hirsch rank `r` has nuclear dimension at
most `r`, with equality whenever its abelianization has rational rank `r`.

Combined instead with Eckhardt--Wu's uniform virtually-polycyclic bound, the
same limit theorem proves `stw84-locally-virtually-polycyclic-uniform-hirsch`:
uniformly bounded Hirsch length across all finitely generated subgroups is
enough for finite nuclear dimension, even when the countable union is not
itself virtually polycyclic or virtually solvable.

A different limit mechanism now passes beyond local virtual polycyclicity.
`stw84-abelian-by-local-virnil-bound` takes a finite-rational-rank countable
abelian group `A` and an arbitrary action of a countable uniformly locally
virtually nilpotent group `H`.  Dualizing `A` turns every finitely generated
actor stage into an arbitrary virtually nilpotent action on the
finite-dimensional compact space `A_hat`.  Hirshberg--Wu's long-thin-cover
estimate is uniform in the action, and therefore survives the subgroup
limit.  If `rank_Q(A)=r` and all local Hirsch lengths are at most `s>=1`, the
result is

```text
dim_nuc C*(A rtimes H) <= 2 s! 9^(s^2) (r+1)^2.
```

For locally finite `H` the bound improves to `r`, while for locally cyclic
`H` it improves to `2r^2+6r+4`.  In particular

```text
1 <= dim_nuc C*(BS(1,n)) <= 12       (n>=2).
```

The expanding normal subgroup `Z[1/n]` is not finitely generated, so these
finitely generated groups are not virtually polycyclic and were not reached
by the existing uniform-local-polycyclic, locally-finite-kernel, or wreath
lanes.

The same limit mechanism now reaches shift semidirect products whose finite
stages are not virtually polycyclic.  The theorem
`stw84-locally-finite-lamp-wreath-bound` says that if `L` is any countable
locally finite group and every finitely generated subgroup `V` of `H` has
polynomial growth of degree at most `D`, then

```text
dim_nuc(C*(L wr H)) <= 2 * 9^D.
```

This is the exact parameter in Eckhardt--Wu's finite-stage bound.  Gromov's
theorem makes the polynomial-growth stages virtually nilpotent, and a
simultaneous lamp/actor exhaustion makes the estimate uniform.  The
Bass--Guivarc'h inequalities `h(V)<=d(V)<=h(V)^2` recover the previous
`2*9^(r^2)` estimate from a uniform local Hirsch bound `r`.  The bound is
independent of the orders and noncommutative representation theory of the
finite lamp stages.  In particular `(direct_sum_N A_5) wr Q` has `D=1` and
nuclear dimension at most `18`, has an infinite nonabelian lamp group, and is
not locally virtually polycyclic.

Regularity of the shift can be weakened substantially.
`stw84-almost-free-permutation-wreath-bound` treats generalized permutation
wreath products `(direct_sum_S L) rtimes A`, where `A` is countable abelian
of finite rational rank `r` and every point stabilizer in `S` is finite.  It
proves the uniform estimate `(r+1)9^r-1` for `r>=1`, and exact dimension zero
for `r=0`.  A torsion-free finite-index
subgroup of each finite-stage actor acts freely on `S`; after choosing orbit
representatives, every non-scalar stabilizer fiber is an ordinary Bernoulli
shift with a matrix or UHF seed.  Scalar fibers contribute `C*(N)` and cost
at most the actor rank, which accounts for the factor `r+1`.  This allows
nontrivial, nonuniform finite stabilizers and examples where finitely
generated subgroups meet the lamp kernel infinitely, beyond both the regular
wreath and kernel-finite hypotheses.

Infinite stabilizers are now covered when their positive-rank part is a
common split core.  `stw84-common-stabilizer-wreath-bound` takes
`A=H direct_sum Q`, lets `H` fix every lamp site, and assumes only finite
stabilizers for the residual `Q`-action.  If `h=rank(H)` and `q=rank(Q)>=1`,
then

```text
h+q <= dim_nuc C*((direct_sum_S L) rtimes A)
    <= (h+1)(q+1)9^q-1.
```

For `q=0` the exact value is `h`.  The proof extracts the trivial directions
as the tensor factor `C*(H)` and applies the corrected scalar/non-scalar
fiber estimate to the residual action.  Thus every point stabilizer may be
infinite of rank `h`; only the orbit-dependent positive-rank case without a
common split core remains outside this mechanism.

The splitting hypothesis can now be removed, and the stabilizers themselves
may vary.  `stw84-commensurable-stabilizer-wreath-bound` assumes a subgroup
`H<=A` fixes every lamp site and only that every residual stabilizer `A_s/H`
is finite.  The extension `0 -> H -> A -> A/H -> 0` need not split.  Each
finite-stage stabilizer crossed product is decomposed over the dual of its
central subgroup `N intersection H`; the resulting fibers are scalar-twisted
almost-free Bernoulli crossed products.  Strong outerness handles the
non-scalar fibers, while Eckhardt--Wu's twisted virtually-polycyclic theorem
uniformly handles the scalar fibers.  This gives a finite rank-dependent
bound, and gives the exact value `rank(H)` when `A/H` has rank zero.  Thus a
finite menu of pairwise commensurable positive-rank stabilizer types is also
covered by taking their intersection.  The remaining orbit-dependent
boundary requires stabilizers with no common finite-index core.

The common-core hypothesis can now be removed completely when there are
only finitely many distinct stabilizers.
`stw84-finite-stabilizer-menu-wreath-bound` assumes merely that
`{A_s:s in S}` is a finite set of subgroups.  For `r=rank_Q(A)>=1`, it gives

```text
r <= dim_nuc C*((direct_sum_S L) rtimes A)
  <= 2(r+1)9^r-1,
```

and rank zero again gives exact dimension zero.  At a finite-stage fiber,
the intersection `J` of the active stabilizer types acts trivially and is
extracted as the central field base.  A simultaneous saturation lemma then
produces a finite-index free lattice whose intersection with each residual
stabilizer is pure.  Every nonzero lattice element consequently has an
infinite orbit through some non-scalar tensor block, giving strong
outerness.  This includes `Z^2` acting on the disjoint union of its two
coordinate-axis coset spaces: the two infinite stabilizers have trivial
intersection and are not commensurable.  The theorem complements, rather
than contains, the earlier result allowing infinitely many distinct finite
stabilizers.

There is also an exact permanence theorem independent of virtual abelianness.
`stw84-locally-finite-direct-factor-invariance` proves that adjoining any
countable locally finite direct factor changes no nuclear dimension.  Hence
`stw84-locally-finite-times-abelian-computation` computes

```text
dim_nuc(C*(L times A))=rank_Q(A)
```

for every countable locally finite `L` and countable abelian `A`, including
infinite rank and non-virtually-abelian products.

The direct-product hypothesis can now be replaced by a controlled extension
hypothesis.  `stw84-kernel-finite-locally-finite-by-abelian-computation`
proves that an exact sequence

```text
1 -> L -> G -> A -> 1
```

with `L` locally finite and `A` abelian satisfies

```text
dim_nuc(C*(G))=rank_Q(A)
```

whenever every finitely generated `H subset G` has finite `H intersection L`.
This includes nonsplit extensions.  For split extensions it is enough that
every finite subset of `L` has finite orbit-generated hull under every
finitely generated subgroup of `A`.  Cyclically rotating finite blocks of
unbounded size gives a nontrivial `L rtimes Z` example which is not virtually
abelian but has nuclear dimension exactly one.

## Attempts

The locally finite factor argument depends on the augmentation quotient
`C*(L times H)->C*(H)` and does not survive an arbitrary semidirect product.
The kernel-finite extension theorem does not itself cover shift actions,
where a finitely generated subgroup can meet the locally finite kernel in an
infinite group.  The new wreath theorem handles regular shifts with any
countable locally finite lamp group when the acting group has uniformly
bounded local polynomial-growth degree (equivalently, local virtual
nilpotence with uniformly bounded local Hirsch length).  The finite-stabilizer
permutation theorem extends this to arbitrary almost-free permutation shifts
for finite-rank abelian actors, but infinite stabilizers break its free-orbit
fiber regrouping.  The commensurable-stabilizer theorem handles a possibly
nonsplit positive-rank core shared with finite index by all stabilizers.  The
finite-menu theorem now handles arbitrary finitely many stabilizer types,
even with no common positive-rank core.  What remains uncontrolled is an
infinite menu of infinite stabilizers with no common finite-index core; its
mixed homogeneous-space tensor fibers cannot be purified by one finite
lattice calculation.
The directed-union argument still gives no control when its finite-stage
bounds diverge.  Thus the remaining frontier includes unrestricted
locally-finite-by-abelian groups, abelian-by-amenable groups whose finitely
generated actors have unbounded nilpotent complexity, and the general
finite-Hirsch-length elementary amenable conjecture.  The wreath-quotient
theorem gives a robust negative class but does not provide a converse:
absence of such a quotient is not known to imply finite nuclear dimension.
