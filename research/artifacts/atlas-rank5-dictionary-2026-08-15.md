# The rank-five factorization dictionary, and the degree-nine screen

Date: 2026-08-15 (evening).  Working notes, not canonical.  Companion to
`notes/ATLAS_RELATOR_EXTRACTION_2026-08-15.md`; same setting and notation

```
Pbar = K1 * K2 = A8 * A8  --rhobar-->>  Q = L_(F2)(1,2)^times
Rbar = ker rhobar,   Nbar = [Pbar, Rbar],   Pbar/Nbar = U_Q
```

and `X` = the twelve adjacent transvections, six per factor.

---

## 1. Step 2 of `atlas-steinberg-rank-five-translation` is DONE

**All 100 rank-five Steinberg generators are now explicit words in `X`, each
verified exactly against its Leavitt target.**

### 1.1 The code

Take the *join* of the two atlas charts as the rank-five prefix code:

```
E = (E_1,...,E_5) = (000, 001, 010, 011, 1)
                  = (gamma_1 e, gamma_1 f, gamma_2 e, gamma_2 f, gamma_3)
```

over the rank-three code `gamma = (00, 01, 1)` of `EXPLICIT_LEAVITT_ATLAS.md`
§1.  `E` is a complete prefix code of size five, so `Theta_E` identifies
`M_5(L)` with `L` and `E_5(L)` with `Q`.

This is the choice the chart-overlap theorem warned about, and the warning is
now precisely located: `E` refines `D_1` and `D_2` **non-uniformly**, so
`GL(E)` contains neither `K1` nor `K2`.  That turns out to be **irrelevant**.
The criterion needs each `x_kl(b)` to be a *word* in `K1 cup K2`, not to lie in
a chart.  The uniform-refinement obstruction blocks the chart-containment
route, not the factorization route.

### 1.2 The mechanism

Write `p(k)` for the rank-three parent index of `E_k` and `s_k` for its suffix
(`p = (1,1,2,2,3)`, `s = (e,f,e,f,-)`).  Then

```
E_k b E_l^* = gamma_{p(k)} ( s_k b s_l^* ) gamma_{p(l)}^* .
```

**Case A, `p(k) != p(l)` (80 of the 100).**  The target lies in the abelian
root subgroup `U_ij(c) = 1 + gamma_i c gamma_j^*`, which is a homomorphic image
of `(L,+)`, and its coefficient `c = s_k b s_l^*` is a product of **at most
three** letters of `S cup {1} = {1,e,f,e^*,f^*}`.  Iterating the Steinberg
identity `[U_ik(a), U_kj(b)] = U_ij(ab)` over the three rank-three indices
reaches every such product from the thirty rank-three generators, which are
already explicit atlas words (`atlas_two_chart_search.q`: twenty are single
chart transvections, ten come from the identities (7) of §3).

`c` is never zero: the letter pattern is always
`[unstarred][b][starred]`, and a product of `S`-letters vanishes only across a
`starred -> different unstarred` adjacency, which cannot occur in that pattern.

**Case B, `p(k) = p(l)` (the 20 with `(k,l)` in `{(1,2),(2,1),(3,4),(4,3)}`).**
Route through index five, whose parent differs from both:

```
x_kl(b) = [ x_k5(b), x_5l(1) ].
```

Index five -- the leaf `gamma_3 = f`, the one leaf the two charts share -- is
the hinge of the whole dictionary.

### 1.3 Result

`experiments/atlas_relator_rank5_dictionary.py`:

```
rank-five generators built: 100
verified exactly:           100
syllable length: min 1  max 17  total 868
X-length:        min 1  max 92  total 3412
recipes: U_12 20, U_21 20, U_13 10, U_23 10, U_31 10, U_32 10,
         [x_k5(b), x_5l(1)] 20
```

Verification is exact binary Leavitt arithmetic against the target
`1 + E_k b E_l^*`; no step is taken on trust.  The dictionary is compact: the
median generator is a short commutator, and the 92-letter worst case is a
three-factor coefficient nested two deep.

---

## 2. The rank-five Steinberg relation family

`experiments/atlas_relator_rank5_relations.py` mirrors, at rank five, the
rank-three family already in `atlas_two_chart_search.relation_family()`:
for each ordered triple `(i,j,k)` of distinct indices, the Steinberg
multiplication relations `stL`/`stR`, the Cuntz relations `e^*e = f^*f = 1`,
the vanishing relations `e^*f = f^*e = 0`, the partition relation
`ee^* + ff^* = 1`, and the root-orthogonality commutators.

Every emitted word is **verified exactly to lie in `Rbar`**.

### The consistency check that matters

By `atlas-kernel-window-length-nine`, every usable relator list must contain a
word **outside** `ker((p_1,p_2) : Pbar ->> A8 x A8)`.  So if the rank-five
family were entirely inside that cartesian subgroup, either the dictionary or
the family would be wrong.  On the six-triple smoke run:

```
distinct nonidentity relators:      83
verified to lie in Rbar:            83 of 83
relators with nontrivial (p1,p2):   11 of 83
syllable length: min 9   max 139
X-length:        min 11  max 465
```

**The family escapes the cartesian subgroup.**  This is the first independent
confirmation that the two halves of this session's work agree: the obstruction
theorem says a usable list must reach X-length 9, and the Steinberg family
independently produces relators that do.

Full-run figures (all 60 triples plus root orthogonality) are in
`experiments/atlas-rank5-relations.json`; see §4.

### What remains for Step 3

The family is a *candidate* presentation.  Usability needs

```
T_St presents St_5(L) over the atlas
   => Rbar/<<T_St>> = K_2(5,L), central by Kervaire-Steinberg
   => Nbar <= <<T_St>>                        (atlas-relator-central-sufficiency)
```

so the open half is **completeness of the relation family as a presentation of
`St_5(L)` over the finite ring presentation**
`L = F2<e,f,e^*,f^*>/(e^*e = f^*f = 1, e^*f = f^*e = 0, ee^* + ff^* = 1)`.
That is the Krstic--McCool input and is a literature-transcription premise, not
verified in repo.  Nothing else is missing: the coefficient set is closed under
the relations used, and the translation is exact and machine-checked.

---

## 3. Finite-quotient screen: the degree-nine case

The Goursat analysis of `ATLAS_RELATOR_EXTRACTION_2026-08-15.md` §(b) left one
family unscreened: `F0 = <alpha(A8), beta(A8)>` with both restrictions
injective and the images neither equal nor commuting.  Two observations reduce
it sharply.  Put `n = [F0 : alpha(A8)]`.

* If `beta(A8) <= alpha(A8)` then `F0 = alpha(A8)`: the fold case, already
  screened (0 of 40320 survive).  Otherwise `beta(A8) cap alpha(A8)` is proper
  in a copy of `A8`, so `n >= 8`, the minimal index of a proper subgroup of
  `A8`.
* `n = 8` is impossible.  The kernel `N` of the degree-eight action meets
  `alpha(A8)` trivially (otherwise `alpha(A8)` is normal and the perfect
  `beta(A8)` lands inside it), so `|N| <= 8` and `A8 -> Aut(N)` is trivial;
  then `alpha(A8) N = alpha(A8) x N`, and `beta(A8)`, being perfect, projects
  isomorphically into `alpha(A8)`, forcing `beta(A8) = alpha(A8)`.

**So the smallest genuinely uncovered case is `n = 9`, where `F0` is transitive
of degree nine with an `A8` point stabiliser, i.e. `F0 = A9`.**

Since the minimal faithful permutation degree of `A8` is 8, every `A8` subgroup
of `A9` is a point stabiliser, so up to global conjugacy `alpha = iota` is
fixed and every injective `beta` is `conj_d . iota . graph^eps` with `d in A9`,
`eps in {0,1}`: exactly `2 * 181440 = 362880` pairs, enumerated exhaustively.

There is no computer-algebra system on the MSI nodes (no `gap` module, no
binary), so `iota : GL_4(F2) -> A8` is built from scratch:
find a subgroup of order 2520 by random search, then take the action on its
eight cosets.  **Trap recorded:** the right-coset action is an
*anti*-homomorphism for the composition `(p*q)(i) = p(q(i))`; each value must be
inverted.  A positive control caught this (see §5).

Result: see §4.

---

## 4. Runs

MSI, `amdsmall` partition via `msi sub` (sioux/acn112/acn116 avoided, held by a
peer's compile loop).  Job logs under
`experiments/atlas-a9-screen-*.log` and `experiments/atlas-rank5-relations-*.log`.

| job | id | outcome |
|:--|:--|:--|
| A9 screen, windows through radius 5 | 15857813 | **0 survivors of 362880**, 76 s |
| rank-five dictionary + relation family | 15857924 | see log |

**Degree-nine screen verdict: PASSES.**  All `362880` pairs of injective
homomorphisms `A8 -> A9` were tested; none kills the enumerated kernel windows
through radius 5.  Stage 1 (the twenty radius-2 commuting conditions,
vectorised over `A9`) already eliminates every pair, in both the inner and the
graph-twisted sector.

Screen status for the radius-5 window is now:

| family of finite quotients | status |
|:--|:--|
| one factor restriction trivial: `A8 x A8` and quotients | passes (radius 5); FAILS at radius <= 4 |
| both injective, equal image: 40320 folds onto `A8` | passes |
| both injective, commuting images | subsumed by `A8 x A8` (Goursat) |
| `n = [F0 : alpha(A8)]` in `{2,...,8}` | impossible (proved, §3) |
| `n = 9`, i.e. `F0 = A9` | **passes** (this run) |
| `n >= 10`: `A10` (90), `Sp6(2)` (72), `GL5(2)` (496), `M24` (12144), ... | open |

So the smallest finite quotient that could still refute the radius-5 window has
order at least `10 * 20160 = 201600`.  This does not certify the window -- no
enumeration can -- but it removes the cheapest refutations.

---

## 5. Controls, and a bug they caught

Two positive controls are built into the scripts rather than run once by hand.

1. **`iota` is a homomorphism.**  Checked on 400 random products after the
   coset construction.  The first version of the screen failed this: the
   right-coset action gives `iota(gh) = iota(h) . iota(g)`.
2. **`p_1` evaluation cross-check.**  Evaluating a window word with `beta`
   trivial is the retraction `p_1`, so it must reproduce `iota(p_1(word))`
   computed independently in `GL_4(F2)`.  This exercises both outcomes: every
   `p_1` is trivial through radius 4, and 118 of the radius-5 words have
   `p_1 != 1`.

The first draft of control 2 asserted the *stronger* statement that `p_1` kills
every window word, and it fired at radius 5 -- correctly, since that is exactly
where the window escapes the cartesian subgroup.  Recording this because the
failure looks like a bug and is not: it is the window-length-nine theorem
showing up in the control.

---

## 6. Files

* `experiments/atlas_relator_rank5_dictionary.py` -- the 100 generators, verified
* `experiments/atlas_relator_rank5_relations.py` -- the Steinberg relation family
* `experiments/atlas_relator_a9_screen.py` -- degree-nine finite-quotient screen
* `experiments/atlas_relator_commuting_pairs.py` -- the cross-chart commuting
  relation and why the uniform argument does not close (see §7)

## 7. Why the screen could not be closed by a uniform argument

If every one-sided partner set `S_y = { x : [x,y] = 1 in Q }` generated `A8`,
then any finite quotient killing the radius-2 window would have commuting
images and the whole uncovered family would be empty.  It does not:

```
y = e12  S_y = {e12,e32}              |<S_y>| =   4
y = e21  S_y = {e21,e23}              |<S_y>| =   4
y = e23  S_y = {e21,e23,e34,e43}      |<S_y>| =  48
y = e32  S_y = {e12,e32,e34,e43}      |<S_y>| =  48
y = e34  S_y = {e23,e32,e34,e43}      |<S_y>| = 168
y = e43  S_y = {e23,e32,e34,e43}      |<S_y>| = 168
```

The commuting relation is symmetric, and the largest partner subgroup is
`GL_3(F2)` of order 168 -- the same rank-three corner that carries the
radius-5 boundary (`TF3`/`TF4` of `atlas_kernel_collision_results.md`).  So the
screen has to be run, not argued.
