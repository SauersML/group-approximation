# Third campaign: finite-image audit and exact cover certificates

Date: 2026-09-20. Scope: independent audit lane. The universal
residual-finiteness problem remains OPEN.

## 1. A bounded classification for the H31 candidate

Let `Q=PSL_2(31)` and let `H_31` be the explicit fivefold triangle
group of CCKW Theorem 1.2. Its vertex groups on `(a,b)`, `(a,c)`,
and `(b,c)` are respectively `Q`, `C_5^2`, and a group of order
`625`. These facts and the exact presentation are recorded in
`rips-central-pullback-finite-image-centers-2026-09-12.md`.

For any map into a finite group with abelian Sylow five subgroups,
the image of the `(b,c)` vertex is abelian, so `[b,c]=1`. Together
with `[a,c]=1`, this makes `c` central in the image. The presentation
after this additional relation is exactly `Q x C_5`.

The simple perfect centerless factor `Q` shows that this direct
product has exactly four quotients: `1`, `C_5`, `Q`, and `Q x C_5`.
All four occur, all have abelian Sylow five subgroups, and all have
order prime to seven. Consequently a central-seven detector for
`H_31` requires a target with nonabelian Sylow five subgroups.

This also excludes all `PSL_2(q)` targets. In characteristic five
their Sylow five groups are additive field groups; in other
characteristics they are cyclic subgroups of a split or nonsplit
torus. This is an elementary order-and-torus argument, not an
appeal to the full classification of subgroups of `PSL_2(q)`.

The new claim and route are `wave3-audit-h31-abelian-sylow-images`
and `wave3-audit-h31-abelian-sylow-proof`. The all-finite condition
`h31-finite-quotients-have-no-seven-schur-class` stays OPEN. No
actual central-seven quotient has been found in this audit.

## 2. Literature scope

The primary source checked is Caprace, Conder, Kaluba, Witzel,
*Hyperbolic generalized triangle groups, property (T) and finite
simple quotients*, JLMS 106 (2022), 3577–3637,
[DOI](https://doi.org/10.1112/jlms.12668), also
[arXiv:2011.09276](https://arxiv.org/abs/2011.09276).
Its explicit H31 construction supports the local data used above.
Its reported searches of finite simple quotients have finite bounds;
its open questions about finite simple quotient types do not
supply a classification of every finite quotient of H31.
No such classification was located in the targeted search.

Independent review: the root agent checked the new four-image
classification against the full H31 presentation and returned PASS.

## 3. Independent audit of the PSL2(19) Borel-square calculation

Let `Lambda -> Q_0^2`, `Q_0=PSL_2(19)`, be the two established
surjections from the previous campaign, let `M` be its kernel,
and let `B<Q_0` be a Borel subgroup of order `171`. Put
`H=preimage(B^2)`. Since `[H:M]=171^2` is prime to five,
restriction `H^2(H;F_5)->H^2(M;F_5)` is injective by transfer.
Thus a twist restricts to zero on `M` if and only if it restricts
to zero on `H`.

The permutation module on `Q_0^2/B^2` has dimension 400 and
represents restriction to `H` by Shapiro. Each vertex group has
orbits of sizes 20 and 380, so its stabilizers have orders 171
and 9. Their first cohomology in characteristic five vanishes.
Each edge group acts freely with 80 orbits of length five.
These are precisely the hypotheses for the already proved
permutation-module moment criterion; regularity of the cover
is unnecessary.

Independently replayed
`experiments/hrf-wave3-detectors-2026-09-20/borel_square_moments.py`
under `/tmp/hrf-wave2-py313/bin/python`. Output: incidence rank 235,
rank after three moment rows 238. The script produces three cycles
with `B lambda=0` and moment vectors equal to the three standard
basis vectors. Therefore all three independent twists remain
nonzero on `M`. This is a theorem about this specified kernel,
not every finite-index subgroup.

Also independently replayed the standard-library-only
`verify_cycles.py`: all 720 orbit-sum equalities and the three
moment vectors pass without using Flint. Reviewed the written
coset-complement lifting argument: a splitting over the possibly
nonnormal H gives an action on central fibres of the coset space,
and conversely evaluation at its H-fixed basepoint is a retraction
of the restricted extension onto its centre. Thus no normality or
torsion-free assumption on H is being hidden in the lifting test.

## 4. Independent audit of the canonical integral class

Replayed and checked
`experiments/hrf-wave3-canonical-class-2026-09-20/stabilizers.py`.
Its exact mod-seven matrices give vertex-kernel orders 49, 343,
343, derived-group orders 1, 7, 7, and exponent seven. Hence all
three abelianizations are `C_7^2`. The enumeration with character
labels also verifies the generator-to-one homomorphism at each
vertex. The derived subgroup is computed as the normal closure
of the commutator of two verified kernel generators.

For `K=ker(G_HB2(7)->C_7)`, all edge and face stabilizers are
trivial and the quotient complex has first homology zero. Its
second integral homology is `Aug Z[C_7]`. The homology spectral
sequence therefore identifies the image of `H_2(K;Z)` in this
augmentation lattice with

```
L = ker(d_2: Aug Z[C_7] -> (C_7)^6).
```

The abelianization of K surjects onto
`ker((C_7)^3 -> C_7)=(C_7)^2`, so the image of `d_2` has rank
at most four. Thus `L/7Aug` is a nonzero deck-invariant submodule
of the six-dimensional augmentation module over `F_7`.
That module is the ideal `(t-1)` in `F_7[t]/(t-1)^7` and is
uniserial. Every nonzero submodule contains its socle
`(t-1)^6=1+t+...+t^6`.

Consequently the coordinate-zero evaluation on L takes a value
nonzero modulo seven. Since `7Aug` lies in L, this evaluation
also takes the value seven, so its image is all of Z. This
proves that the specified face-zero class is primitive as a
homology evaluation. The five-term integral homology sequence
then puts the central generator z of its integral cover in the
commutator subgroup. For any finite image F of that cover,
with A the cyclic image of z, the map `H_2(F/A;Z)->A` is onto.
In particular multiplier-trivial finite quotient bases kill z.
This imposes a detector constraint; it neither bounds all finite
central orders nor constructs unbounded orders.

## 5. Independent audit of the universal Steinberg lift

Reviewed Sections 1--2 of
`hyperbolic-rf-wave3-visibility-2026-09-20.md`: PASS. Over any
associative unital F7-algebra, the positive-root subgroup of the
stable Steinberg group embeds in the elementary matrix group by
ordered root collection. Index permutations give each required
ordering. The `(A,B)` support has no directed path of length three;
the other two pairs have path length three. Their remaining triple
commutators vanish by the checked identity
`[1+P,1+Q]=1+PQ-QP-QPQ`, with `P^2=Q^2=PQP=0`.
Thus all eleven defining relators lift exactly, including for
noncommuting coefficients. Pullbacks and central pushouts of the
stable Steinberg extension consequently split on G and K.

The detector consequence uses the now independently audited
primitivity of c0. The difference between a proposed cover map and
an exact lifted base map is a homomorphism into the central cyclic
kernel, so it kills z in the commutator subgroup. This excludes
the specified stable Steinberg construction. The author's scope
fence correctly leaves arbitrary central extensions of finite
image subgroups untouched.

Also checked the five-term deduction and image-surjectivity
argument in Section 3, conditional on its cited central-closure
theorem, and the entrywise diagonal conjugation and monogenic
ring reduction in Section 4. The full Hesselholt--Madsen theorem
was not independently reread in this lane; that citation remains
an ancillary explanation rather than an input to Sections 1--2.
