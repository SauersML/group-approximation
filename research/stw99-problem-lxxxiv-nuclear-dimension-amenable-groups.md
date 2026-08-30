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
  - research/artifacts/stw84-arbitrary-stabilizer-wreath-2026-08-30.md
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

In fact, the global finite-menu hypothesis can now be removed entirely.
`stw84-arbitrary-stabilizer-permutation-wreath-bound` applies to every
permutation action of a finite-rational-rank countable abelian group `A` on
a countable set, with no restriction on the point stabilizers, and retains
the same estimate

```text
rank_Q(A) <= dim_nuc C*((direct_sum_S L) rtimes A)
          <= 2(rank_Q(A)+1)9^rank_Q(A)-1.
```

The reason is a finite-stage principle hidden by the global formulation:
the invariant hull of finitely many lamp sites under a finitely generated
actor subgroup is a finite union of orbits, and abelianness makes the
stabilizer constant along each orbit.  Every stage therefore has a finite
menu automatically.  The simultaneous-purification index can diverge along
the exhaustion, but the finite-menu dimension bound is independent of it.
This covers, for example, `Z^2` acting on the disjoint union of `Z^2/H_n`
for all slope subgroups `H_n=Z(1,n)`, an infinite family of infinite,
pairwise noncommensurable stabilizers with no common positive-rank core.

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

The unrestricted extension problem now has an exact torsion-absorption
reduction.  `stw84-locally-finite-by-abelian-reduces-to-twisted-af-lattices`
shows that the inverse image `K` of `tor(A)` is locally finite.  After
replacing the quotient by the torsion-free group `A/tor(A)`, an exhaustion
by free lattices gives

```text
C*(E_j)=C*(K) rtimes_(alpha_j,u_j) Z^(q_j),
q_j<=rank_Q(A),
```

with `C*(K)` AF and a group-unitary Busby--Smith cocycle.  This solves rank
zero completely, with no kernel-finite hypothesis.  In rank one every
cyclic stage splits, so the exact remaining core is a uniform bound for
`C*(K rtimes_alpha Z)` over arbitrary locally finite `K` and automorphisms
`alpha`.  Here kernel-finiteness is equivalent to an exhaustion of `K` by
finite `alpha`-invariant subgroups.  The two-generated shift group
`Alt_fin(Z) rtimes Z` fails this condition maximally and has overlapping,
noncommuting shifted seeds, so neither the finite-kernel nor the permutation-
wreath mechanism reaches the residual cyclic core.

The whole cyclic core nevertheless has a new operator-algebraic regularity
theorem.  `stw84-cyclic-local-finite-af-embeddable`
proves that every `C*(K rtimes_alpha Z)` is AF-embeddable and quasidiagonal:
amenability supplies a faithful regular trace and hence stable finiteness,
so Brown's AF-coefficient theorem applies.  The augmentation character also
gives the exact sequence

```text
0 -> I_K rtimes_alpha Z -> C*(K rtimes_alpha Z) -> C(T) -> 0.
```

Thus the nuclear-dimension question is concentrated in the nonunital
augmentation-ideal crossed product; a bound `d` there gives `d+2` globally.
Ordinary Rokhlin dimension cannot provide it, since augmentation is an
equivariant quotient onto the trivial scalar action, whose Rokhlin dimension
is infinite.  In the alternating-shift stress test the AF automorphism is
even approximately inner, although one three-cycle still has infinite orbit
hull.  Approximate innerness therefore does not recover the finite-kernel
exhaustion.

The augmentation ideal now has explicit finite-dimensional Følner carriers.
For a finite subgroup `F<=K`, the complementary averaging projection

```text
e_F=1-|F|^(-1)sum_(g in F)lambda_g
```

is the identity on the finite-group augmentation ideal.  Averaging its
`alpha`-translates over a long interval produces a finite-spectrum positive
contraction `h` in one finite group algebra which carries any prescribed
finite coefficient set exactly and satisfies
`||alpha^k(h)-h||<=|k|/N`.  Diagonalization gives a quasicentral approximate
unit for `I_K rtimes_alpha Z`
(`stw84-augmentation-ideal-has-finite-dimensional-folner-carriers`).  Its
support projection `s` gives an exact local corner `s(I_K rtimes Z)s`, so a
uniform bound on these carrier corners would settle the cyclic core.  The
remaining seam is sharp: the smallest positive eigenvalue of `h` can tend
to zero, and consequently almost invariance of `h` gives no norm control on
`alpha(s)-s`.

The support corner is now identified exactly, and this closes another false
shortcut.  If `H` is the finite subgroup generated by the orbit window in
the carrier average, then

```text
supp(h)=e_H,
Ideal_(C*(G))(e_H)=ker(C*(G)->C*(G/normal_closure_G(H))).
```

Thus `e_H(I_K rtimes Z)e_H` is a full corner of the normal-closure
augmentation ideal
(`stw84-folner-carrier-corners-are-normal-closure-corners`).  For the
alternating shift, simplicity of `Alt_fin(Z)` makes every nonzero carrier
corner full in the entire unresolved ideal.  Its nuclear dimension is
therefore exactly the unknown quantity one started with.  Any successful
carrier argument for that stress test must retain the positive eigenvalue
weights of `h`; passing to support is Morita-tautological.

Keeping those weights does give an exact finite-packet retraction.
`stw84-weighted-fourier-cutdown-and-row-gap` proves that
`x |-> h^(1/2)x h^(1/2)` recovers every prescribed Fourier monomial
`aU^k` within `||a||sqrt(|k|/N)`.  This bypasses the discontinuous support
projection entirely.  The canonical unsplit Fourier-row return map cannot,
however, supply one order-zero colour: balanced complementary diagonal
projections give a uniform distance at least `1/9` from every c.p.c.
order-zero map.  The next construction must therefore split the Fourier
window into genuinely different colours rather than perturbing the usual
row map through cone projectivity.

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
for finite-rank abelian actors, and the finite-menu theorem handles arbitrary
finitely many infinite stabilizer types.  Passing to finite unions of actor
orbits at each approximation stage now removes the menu restriction
altogether: arbitrary permutation wreath products by finite-rank abelian
actors have finite nuclear dimension.
The directed-union argument still gives no control when its finite-stage
bounds diverge.  Thus the remaining locally-finite-by-abelian frontier is
already the arbitrary AF-automorphism cyclic core above.  Other remaining
families include abelian-by-amenable groups whose finitely
generated actors have unbounded nilpotent complexity, and the general
finite-Hirsch-length elementary amenable conjecture.  The wreath-quotient
theorem gives a robust negative class but does not provide a converse:
absence of such a quotient is not known to imply finite nuclear dimension.
