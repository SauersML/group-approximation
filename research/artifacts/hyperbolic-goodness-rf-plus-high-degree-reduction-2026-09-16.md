# Universal goodness of hyperbolic groups = universal residual finiteness + high-degree effacement

Swarm lane `every-hyperbolic-group-is-good`, 2026-09-16. Unreviewed; not Lean-verified.
No priority is claimed for any individual lemma: Section 1 is Serre's exercise
(Galois Cohomology, Ch. I, §2.6, Exercises 1-2, recalled, not fetched), Section 2 is
the classical extension argument used by Grunewald--Jaikin-Zapirain--Zalesskii and by
`finite-central-extension-rf-iff-virtually-splits`. What is organized here is the exact
split of `every-hyperbolic-group-is-good` into two assertions, one of which is
Gromov's question.

## 0. Conventions and standard facts

Throughout, `G` is a group, `G_hat` its profinite completion, and a *finite
`G`-module* is a finite abelian group `M` with a `G`-action whose kernel has finite
index. `N(G;M)` denotes the set of finite-index normal subgroups `U` of `G` acting
trivially on `M`; it is directed under reverse inclusion.

A class `x in H^q(G;M)` is **effaceable** if `res^G_W(x) = 0` for some finite-index
subgroup `W <= G`. Shrinking `W` to its normal core intersected with the kernel of the
action, `W` can be taken in `N(G;M)`.

**(E_n)** for `G`: for every finite `G`-module `M` and every `1 <= q <= n`, every
class in `H^q(G;M)` is effaceable.

**(A_n)** for `G`: for every finite `G`-module `M` and every `0 <= q <= n`, the
inflation `inf_q: H^q(G_hat;M) -> H^q(G;M)` is an isomorphism.

`G` is **good** iff `(A_n)` holds for all `n`.

Standard facts used, all textbook:

- **(F1) Colimit description.** For a finite `G`-module `M`,
  `H^q(G_hat;M) = colim_{U in N(G;M)} H^q(G/U;M)` with inflation transition maps, and
  `inf_q` is the colimit of the inflations `H^q(G/U;M) -> H^q(G;M)`. (Serre, Galois
  Cohomology I.2.2, Prop. 8; open normal subgroups of `G_hat` are the kernels of
  `G_hat -> G/U`.) This is the same description used in
  `good-no-persistent-cohomology-proof`.
- **(F2) Long exact sequences.** A short exact sequence `0 -> M -> M* -> M'' -> 0` of
  `G/U`-modules gives long exact sequences for `G/V` (every `V in N(G;M*)`, `V <= U`)
  and for `G`; inflation commutes with all maps, including the connecting maps, since
  it is induced by a map of cochain complexes natural in the module. Directed colimits
  of exact sequences are exact, so the colimit sequence for `G_hat` is exact and `inf`
  is a map of long exact sequences.
- **(F3) Shapiro.** For `U` normal of finite index in a group `Γ` acting trivially on
  `M`, let `M* = Map(Γ/U, M)` with the diagonal action `(g f)(x) = g f(g^{-1}x)`, unit
  `η: M -> M*` (constant functions, `Γ`-equivariant) and evaluation
  `ε: M* -> M`, `ε(f) = f(U)` (`U`-equivariant), so `ε∘η = id`. Then
  `σ = ε_* ∘ res^Γ_U : H^q(Γ;M*) -> H^q(U;M)` is an isomorphism (Brown, Cohomology
  of Groups, III.5-III.6: `Φ(f)(h) = h f(h^{-1}U)` identifies `M*` with
  `Coind_U^Γ M`, and `ψ∘Φ = ε`). Moreover `σ∘η_* = (ε∘η)_*∘res = res^Γ_U`.
- **(F4) Extensions.** `H^2(G;M)` classifies extensions `1 -> M -> E -> G -> 1`
  inducing the given action; restriction to `W` corresponds to pulling back to
  `π^{-1}(W)`, inflation along `G -> Q` to pulling back along that map, and the zero
  class to split extensions (Brown IV.3).
- **(F5) Hyperbolicity.** Finite-index subgroups and extensions with finite kernel of
  a word-hyperbolic group are word-hyperbolic (quasi-isometry invariance). A
  torsion-free hyperbolic group has a finite `K(π,1)` (Rips complex), hence finite
  cohomological dimension.

## 1. Effaceability makes inflation an isomorphism

**Proposition 1.** For every group `G` and every `n >= 0`, `(E_n)` implies `(A_n)`.
In particular a group all of whose positive-degree finite-coefficient classes are
effaceable is good.

*Proof.* Induction on `n`.

*Base `n = 0`.* By (F1), `H^0(G_hat;M) = colim_U M^{G/U} = M^G` (every `U in N(G;M)`
acts trivially), and `inf_0` is the identity of `M^G`. So `(A_0)` holds for every
group, with no hypothesis.

*Step.* Let `n >= 1` and assume `(E_n)`. Then `(E_{n-1})` holds, so `(A_{n-1})` holds
by induction. Fix a finite `G`-module `M`. We show `inf_n` is bijective.

*Set-up for a given `U in N(G;M)`.* Put `M* = Map(G/U, M)` with the diagonal action,
`η: M -> M*` and `ε` as in (F3), and `M'' = M*/η(M)`. All three are finite `G`-modules
on which `U` acts trivially (`(u f)(x) = f(u^{-1}x) = f(x)` since `U` is normal and
acts trivially on `M`). By (F2) there is a commutative ladder with exact rows

```text
H^{n-1}(G_hat;M*) -> H^{n-1}(G_hat;M'') -δ^-> H^n(G_hat;M) -η^-> H^n(G_hat;M*)
      | a                  | b                  | c = inf_n        | d
H^{n-1}(G;M*)     -> H^{n-1}(G;M'')     -δ->  H^n(G;M)    -η->  H^n(G;M*)
```

where `a, b` are isomorphisms by `(A_{n-1})` applied to the finite modules `M*`,
`M''`.

*Surjectivity of `c`.* Let `x in H^n(G;M)`. By `(E_n)` choose `U in N(G;M)` with
`res^G_U(x) = 0`, and build the ladder for this `U`. By (F3),
`σ(η_*(x)) = res^G_U(x) = 0` with `σ` injective, so `η_*(x) = 0`. By exactness
`x = δ(w)` for some `w in H^{n-1}(G;M'')`. Since `b` is onto, `w = b(ŵ)`, and then
`c(δ^(ŵ)) = δ(b(ŵ)) = x`.

*Injectivity of `c`.* Let `y in H^n(G_hat;M)` with `c(y) = 0`. By (F1), `y` is the
image of some `z in H^n(G/U;M)` with `U in N(G;M)`; build the ladder for this `U`.

First, `η^(y) = 0` in `H^n(G_hat;M*)`. Indeed `η^(y)` is the image in the colimit of
`η_*(z) in H^n(G/U;M*)`. As a `G/U`-module, `M* = Map(G/U, M)` is (F3) for the finite
group `Γ = G/U` and its trivial normal subgroup `U/U`, so
`H^n(G/U;M*) ≅ H^n(U/U;M) = 0` for `n >= 1`. Hence `η_*(z) = 0` and `η^(y) = 0`.

By exactness of the top row, `y = δ^(v)` for some `v in H^{n-1}(G_hat;M'')`. Then
`δ(b(v)) = c(δ^(v)) = c(y) = 0`, so by exactness of the bottom row `b(v)` is the image
of some `w in H^{n-1}(G;M*)`. Since `a` is onto, `w = a(ŵ)`, and commutativity gives
`b(image of ŵ) = b(v)`. Since `b` is injective, `v` is the image of `ŵ` in
`H^{n-1}(G_hat;M'')`, so `y = δ^(v) = 0` by exactness of the top row.

Hence `inf_n` is an isomorphism for every finite `M`; with `(A_{n-1})` this is
`(A_n)`. `QED`

The converse `(A_n) => (E_n)` is `good-no-persistent-cohomology-proof` read degree by
degree; it is not needed below.

## 2. Degrees one and two

**Lemma 2.1.** Every group satisfies `(E_1)`.

*Proof.* Represent `x in H^1(G;M)` by a crossed homomorphism `f`,
`f(gh) = f(g) + g f(h)`. On `U = ker(G -> Aut M)` it is a homomorphism `U -> M`, whose
kernel `W` has finite index in `U`, hence in `G`. `f|_W = 0`, so `res^G_W(x) = 0`.
`QED`

**Lemma 2.2.** Let `M` be a finite `G`-module and `x in H^2(G;M)`, classifying
`1 -> M -> E -π-> G -> 1`. If `E` is residually finite, then `x` is effaceable.

*Proof.* `M` is finite, so finitely many finite-index normal subgroups of `E` separate
its nonidentity elements from `1`; their intersection `E_0` is finite-index normal in
`E` with `E_0 ∩ M = 1`. Put `W = π(E_0)`, of finite index in `G`. `π|_{E_0}: E_0 -> W`
is injective (its kernel is `E_0 ∩ M`) and onto, so its inverse `s: W -> E` is a
homomorphic section of `π` over `W`. So the pullback `π^{-1}(W) -> W` splits and
`res^G_W(x) = 0` by (F4). `QED`

**Corollary 2.3.** If every extension of `G` by a finite `G`-module is residually
finite, `G` satisfies `(E_2)`. If moreover `H^q(G;M) = 0` for all `q >= 3` and all
finite `M` (e.g. `cd G <= 2`), `G` is good.

*Proof.* Lemmas 2.1, 2.2 give `(E_2)`; the vanishing makes `(E_n)` hold for every `n`,
and Proposition 1 applies. `QED`

(Converse, for completeness: if `G` is residually finite and `x` is effaceable on `W`,
then `π^{-1}(W) = M ⋊ s(W)`, so `E` has the finite-index subgroup `s(W) ≅ W`, which is
residually finite, hence `E` is residually finite. So for residually finite `G`,
`(E_2)` is equivalent to residual finiteness of all finite-module extensions; this is
the non-central form of `finite-central-extension-rf-iff-virtually-splits`.)

## 3. Passing through finite index and to trivial `F_p` coefficients

**Lemma 3.1.** If `H <= G` has finite index and `H` satisfies `(E_n)`, so does `G`.

*Proof.* For `x in H^q(G;M)`, `1 <= q <= n`, the class `res^G_H(x)` lies in
`H^q(H;M)` for the finite `H`-module `M`; it vanishes on some finite-index `W <= H`,
and `W` has finite index in `G`; `res^G_W = res^H_W∘res^G_H`. `QED`

**Lemma 3.2.** Let `C` be a class of groups closed under passing to finite-index
subgroups, and fix `q >= 1`. Suppose that for every `H in C` and every prime `p`, every
class in `H^q(H;F_p)` (trivial action) is effaceable. Then for every `H in C` and every
finite `H`-module `M`, every class in `H^q(H;M)` is effaceable.

*Proof.* Restrict to `U = ker(H -> Aut M)`, which lies in `C`; by Lemma 3.1 (applied in
degree `q` only, same proof) it suffices to efface `res(x) in H^q(U;M)` with `M` a
trivial `U`-module. Induct on `|M|`. If `M = 0` there is nothing to do. Otherwise pick
a subgroup `P <= M` of prime order `p`; it is a trivial submodule, `P ≅ F_p`. From
`0 -> P -i-> M -> M/P -> 0` and the induction hypothesis, the image of `x` in
`H^q(U;M/P)` dies on some finite-index `W_1 <= U`; by exactness
`res^U_{W_1}(x) = i_*(y)` for some `y in H^q(W_1;F_p)`. As `W_1 in C`, `y` dies on some
finite-index `W_2 <= W_1`, and `res^U_{W_2}(x) = i_*(res^{W_1}_{W_2} y) = 0`. `QED`

(The induction is over the statement "for all `U in C` and all trivial modules of
order `< |M|`", so the hypothesis is applied to `M/P` on `U` and to `F_p` on `W_1`.)

## 4. The split of universal goodness

**Theorem 4.** The following are equivalent.

1. Every word-hyperbolic group is good.
2. Both:
   - **(a)** every word-hyperbolic group is residually finite; and
   - **(b)** for every torsion-free word-hyperbolic group `H`, every prime `p` and
     every `q >= 3`, every class in `H^q(H;F_p)` (trivial action) vanishes on some
     finite-index subgroup of `H`.

By (F5), (b) is vacuous for `q > cd H`, so only `3 <= q <= cd H` matters.

*Proof of 2 => 1.* Let `G` be hyperbolic. By (a) and `universal-hyperbolic-vtf-iff-rf`
(Wise, Complete square complexes, Prop. 9.2 and Thm 9.3, recorded there), `G` has a
torsion-free finite-index subgroup `H`, which is hyperbolic by (F5). We show `H`
satisfies `(E_n)` for all `n`; then so does `G` (Lemma 3.1), and `G` is good
(Proposition 1).

- `q = 1`: Lemma 2.1.
- `q = 2`: an extension `E` of `H` by a finite `H`-module has finite kernel, so it is
  hyperbolic (F5), hence residually finite by (a); Lemma 2.2.
- `q >= 3`: the class `C` of torsion-free hyperbolic groups is closed under
  finite-index subgroups (F5); by (b) and Lemma 3.2, every class of degree `q` with any
  finite coefficients is effaceable.

*Proof of 1 => 2.* (a): item 3 of `good-cocompact-proper-groups-are-virtually-torsion-free`
gives universal virtual torsion-freeness, and `universal-hyperbolic-vtf-iff-rf` gives
universal residual finiteness. (b): `good-groups-have-no-persistent-finite-cohomology`.
`QED`

So `every-hyperbolic-group-is-good` is exactly Gromov's question (in the positive form
`hyperbolic-finite-residual-is-torsion-free`, equivalent to (a) by
`universal-hyperbolic-vtf-iff-rf`) plus the purely cohomological assertion (b) about
torsion-free hyperbolic groups in degrees `3..cd`. Neither half implies the other by
any argument recorded here: (a) says nothing about degrees `>= 3`, and (b) concerns
only torsion-free groups and so cannot see torsion in finite residuals.

## 5. Two-dimensional hyperbolic groups

**Corollary 5.** Let `G` be hyperbolic with a torsion-free finite-index subgroup `H` of
cohomological dimension `<= 2`. If every extension of `H` by a finite `H`-module is
residually finite, `G` is good. In particular, if (a) holds, every hyperbolic group of
virtual cohomological dimension `<= 2` is good.

*Proof.* `H^q(H;M) = 0` for `q >= 3`, so Corollary 2.3 makes `H` satisfy `(E_n)` for all
`n`; Lemma 3.1 transfers this to `G`, and Proposition 1 applies. Under (a), every
hyperbolic `G` is virtually torsion-free, and the extensions of `H` are hyperbolic,
hence residually finite. `QED`

**Per-group sharpening.** If `G` is residually finite, the hypothesis of Corollary 5 is
also necessary for "`G` good": goodness gives `(E_2)` for `H`, and then each
finite-module extension of `H` has a finite-index subgroup isomorphic to a finite-index
subgroup of `H` (converse paragraph of §2), so it is residually finite. [Referee
addition 2026-09-16, justifying "goodness gives `(E_2)` for `H`": for an `H`-module `M`
and `x in H^2(H;M)`, Shapiro gives `X in H^2(G;Coind_H^G M)` with
`x = ε_*(res^G_H X)`. By `good-groups-have-no-persistent-finite-cohomology`, `X` dies on
some finite-index normal `W <= G`, which may be shrunk into `H`; then
`res^H_W x = ε_*(res^G_W X) = 0`.] Hence for a
hyperbolic `G` with a torsion-free finite-index `H`, `cd H <= 2`:

```text
G is good and residually finite  <=>  every extension of H by a finite H-module is residually finite.
```

(`<=`: the zero module gives `H` residually finite, hence `G`.)

**Example: `GHB_2(7)`.** By `cckw-ghb2-kms-group-structure` items 3-5, `G = G_{HB_2}(7)`
acts simplicially on the CAT(−1), hence contractible, 2-dimensional complex `Y` with a
triangle as strict fundamental domain and finite stabilizers, and `H = ker ψ` is
torsion-free of finite index. `H` meets every stabilizer trivially, so it acts freely
and cocompactly on `Y`; `Y/H` is a finite 2-dimensional `K(H,1)` and `cd H <= 2`. So,
unconditionally, `GHB_2(7)` is good and residually finite iff every finite-module
extension of `ker ψ` is residually finite. For this Kazhdan example, goodness adds
nothing beyond residual finiteness of finite extensions. The content of (b) that is not
already Gromov's question lives in cohomological dimension `>= 3`.

(Density random groups above `1/3`, the other Kazhdan example in the Attempts of
`every-hyperbolic-group-is-good`, are recalled from Ollivier's survey to be torsion-free
with aspherical presentation complexes below density `1/2`; not rechecked here, so they
are not used.)

## 6. Degree two on `GHB_2(7)` needs only residual finiteness

**Lemma 6.** Let `K` be a group, `n >= 1`, and `x in H^2(K;Z/n)` (trivial action),
classifying a central extension `1 -> Z/n -> E -π-> K -> 1`. If `E` is residually
finite, then `x = inf(y)` for some finite-index normal `N` of `K` and
`y in H^2(K/N;Z/n)`.

*Proof.* As in Lemma 2.2 choose `E_0` normal of finite index in `E` with
`E_0 ∩ Z/n = 1`, and put `N = π(E_0)`, normal of finite index in `K`. Put `Q = E/E_0`,
a finite group. `Z/n` maps injectively and centrally into `Q`, and
`Q/(Z/n) = E/(E_0·Z/n) ≅ K/N` (the map `E -> K/N` is onto with kernel
`π^{-1}(N) = E_0·Z/n`). Let `y` classify `1 -> Z/n -> Q -> K/N -> 1`. The map
`E -> P = Q ×_{K/N} K`, `e ↦ (eE_0, π(e))` is a homomorphism restricting to the
identity on `Z/n` and covering the identity of `K`, so it is an isomorphism of
extensions (short five lemma). `P` is the pullback of `Q` along `K -> K/N`, whose class
is `inf(y)` (F4). Hence `x = inf(y)`. `QED`

**Consequence.** Assume (a). Let `K <= G_{HB_2}(7)` be any finite-index subgroup. It is
hyperbolic (`cckw-ghb2-kms-group-structure`, (F5)); each central extension of `K` by
`Z/n` is hyperbolic, hence residually finite; by Lemma 6, `K` has property (G2) of
`degree-two-inflation-onto-makes-z-extension-centres-survive`. With `K = K_7`,
`b_2(K_7;Q) = 6` (`ghb7-normal-subgroup-b2-is-orbit-euler-count`), this is
`ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`. So that claim needs
only the positive answer to Gromov's question, not universal goodness.

## 7. Where (b) stands

These are partial observations, not proofs of (b).

**7.1 Effaceable classes form an ideal.** For any group `H` and prime `p`, the set
`Eff^*(H) ⊆ H^*(H;F_p)` of effaceable classes is a two-sided ideal: a sum of classes
effaced on `W_1, W_2` is effaced on `W_1 ∩ W_2`, and `(x ∪ y)|_W = x|_W ∪ y|_W`.
A graded ideal containing a set of algebra generators of `H^{>=1}(H;F_p)` is all of
`H^{>=1}` (every monomial contains a generator). Under (a), `Eff` contains `H^1` and
`H^2` (Lemmas 2.1, 2.2). So, under (a), (b) for `H` is equivalent to: **each
indecomposable class of degree `>= 3` (one representative per basis element of
`H^{>=3}/(H^{>=1}·H^{>=1})`) is effaceable.** Torsion-free hyperbolic groups whose
mod-`p` cohomology ring is generated in degrees `<= 2` satisfy (b) under (a).
Indecomposables in degree `>= 3` do occur: for a closed hyperbolic 3-manifold with
`H_1(M;F_p) = 0` the top class is not a product. (Those groups are good anyway, by
Kropholler--Wilkes; the example only shows 7.1 does not dispose of (b).)

**7.2 Pullbacks.** If `x = f^*(c)` for a homomorphism `f: H -> Γ` and `c` is effaceable
on `Γ` (on `W`), then `x` is effaceable (on `f^{-1}(W)`). Effaceable `c` arise when `Γ`
is good (e.g. hyperbolic virtually special), or, under (a), when `Γ` is hyperbolic and
`deg c > vcd Γ` (then `c` dies on a torsion-free finite-index subgroup). *Where it dies:*
the groups where (b) is not already known are the non-cubulated ones, notably Kazhdan
groups, and a Kazhdan group has only finite-image homomorphisms to groups acting
properly on CAT(0) cube complexes (fixed-point property, Niblo--Reeves, recalled). So
pullbacks from good cubulated groups give only classes inflated from finite quotients,
which are effaced on the kernel by definition. Pullback from a hyperbolic `Γ` of small
vcd needs a homomorphism `H -> Γ` that is nonzero on a class of degree `> vcd Γ`; no
construction of such maps for Kazhdan `H` is known to us.

**7.3 Top degree of a Poincaré duality group.** If `H` is an orientable `PD^n` group
over `F_p` and `W` has index `d`, then `res^H_W: H^n(H;F_p) -> H^n(W;F_p)` is
multiplication by `d` (the transfer is an isomorphism in top degree and
`cor∘res = d`). So the top class is effaceable iff `H` has a finite-index subgroup of
index divisible by `p`. Under (a) this holds for non-elementary torsion-free
hyperbolic `H`: a deep Dehn filling `H/<<g^m>>`, `p | m`, is hyperbolic with `g` of
order `m` (the filling theorem used in `hyperbolic-rf-question-equals-vtf-question`),
hence residually finite by (a), so some finite quotient of `H` contains an element of
order `p`. This disposes of the top degree only; degrees `3..n-1` of `PD^n` groups
(e.g. torsion-free cocompact lattices in `Sp(n,1)`, `n >= 2`, cd `4n`) are untouched.

**7.4 The natural test case.** Torsion-free cocompact lattices `Γ` in `Sp(n,1)`
(`n >= 2`) and in `F_4^{(-20)}` are hyperbolic, Kazhdan, linear (so residually finite)
and of cohomological dimension `>= 8`. For such `Γ`, goodness is equivalent to (b) on
`Γ` and its finite-index subgroups (Lemma 3.2 with `C` = finite-index subgroups of `Γ`)
*together with* residual finiteness of every finite-module extension of `Γ` (§2,
converse paragraph); residual finiteness of `Γ` itself does not give the degree-two
half. [Referee correction 2026-09-16: the earlier wording "for them (b) is exactly
goodness" omitted the degree-two condition.] We found no
source proving or disproving goodness for them (searches of 2026-09-16, Section 8).
A persistent class in some degree `3 <= q <= cd Γ` on such a lattice would refute
`every-hyperbolic-group-is-good` without touching Gromov's question. One natural
diagnostic is the growth of `H^q(Γ_i;F_p)` along towers; we did not compute it and do
not know which way it points.

## 8. Literature and status (checked 2026-09-16)

- Grunewald, Jaikin-Zapirain, Zalesskii, *Cohomological goodness and the profinite
  completion of Bianchi groups*, Duke Math. J. **144** (2008) 53-72,
  DOI 10.1215/00127094-2008-031 (bibliographic data and abstract fetched from Project
  Euclid 2026-09-16). Goodness of Bianchi groups; residual finiteness of central
  extensions of Fuchsian groups as the application, the same mechanism as Lemma 2.2.
- Kropholler--Wilkes, arXiv:1603.07197, Theorem 9 (recorded on
  `good-groups-have-no-persistent-finite-cohomology`, checked there 2026-08-30).
- S. Hughes and A. Ng, *Cobordism, spin structures, and profinite completions*,
  arXiv:2601.05706 (9 January 2026), fetched 2026-09-16: lists virtually compact special
  groups as good (via Wilton--Zalesskii Prop. 3.2) and does not assert goodness of all
  hyperbolic groups.
- M. Boggi and P. Zalesskii, *Finite subgroups of the profinite completion of good
  groups*, arXiv:2406.08639 (v1 12 June 2024, v2 28 October 2024; Bull. LMS 2025),
  abstract fetched 2026-09-16: applications to virtually compact special groups; no
  claim about all hyperbolic groups.
- Web searches on 2026-09-16 for statements that every hyperbolic group is good, or for
  goodness of `Sp(n,1)` lattices, found no resolution and no explicit problem-list entry.
  So we still cannot cite a named source posing universal goodness as a problem. Its
  open status follows from the graph: it implies a positive answer to Gromov's question
  (`good-cocompact-proper-groups-are-virtually-torsion-free`), which Cui--Wan,
  arXiv:2604.04007 (5 April 2026), still call open (recorded on
  `non-residually-finite-hyperbolic-group`, checked 2026-09-07).
- Serre, *Galois Cohomology*, Ch. I §2.6, Exercises 1-2 (effaceability criterion) and
  Brown, *Cohomology of Groups*, III.5-III.6, IV.3: recalled, not fetched. Section 1
  proves the direction we need rather than relying on the exercise.
