# Extracting the finite relator list for the canonical regular-`A8` criterion

Date: 2026-08-15.  Working notes, not canonical.  Nothing here is committed to
`notes/` or `research/`.

Setting, throughout, is `notes/EXPLICIT_LEAVITT_ATLAS.md:458-607` (§9):

```
Pbar = K1 * K2 = A8 * A8   --rhobar-->>  Q = L_(F2)(1,2)^times
Rbar = ker rhobar,   Nbar = [Pbar, Rbar],   Pbar/Nbar = U_Q   (22)
```

`X` is the twelve-element generating set of six adjacent transvections
`e_12,e_21,e_23,e_32,e_34,e_43` per factor
(`notes/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md:28-40`).  "X-length" always means
word length in `X`; in a free product it is additive over free-product
syllables, so it is the sum of the six-transvection lengths of the
`GL_4(F2)` syllables.

---

## (a) What the criterion actually requires of a candidate list

§9 fixes `Sbar ⊆ Nbar` normally generating `Nbar` (24).  That is much more
than the theorem uses.  Read the two directions separately.

**Necessity (1 => 2), §9 lines 550-590.**  The pulled-back hyperlinear model
kills `Rbar` *exactly*; HS-stability of the virtually free `Pbar` corrects it
to exact representations of the canonical form (25) changing every **fixed**
word by `o(1)`.  The doc says this itself: "Since the original pulled-back
models kill `Rbar`, they kill (24) asymptotically".  So the argument never
uses `Sbar ⊆ Nbar`, only `Sbar ⊆ Rbar`.

**Sufficiency (2 => 1), §9 lines 592-607.**  (26) makes
`Pi : Pbar -> prod_omega U(20160 k_n)` a homomorphism with
`<<T>> <= ker Pi`.  The rest of the proof needs only that
`V = Pbar/<<T>>` is perfect and central over the simple `Q`; the
identification with `U_Q` is never used.  (`FALSE_RECURSIVE_ATLAS_EXHAUSTION.md:566-568`
already records exactly this remark for its own Theorem 4.)

Hence:

> **Usability criterion.**  Let `T ⊆ Pbar` be finite.  The equivalence
>
>   `Q` hyperlinear  <=>  there are `k_n >= 1`, `U_n in U(20160 k_n)` with
>   `max_{t in T} ||pi_(k_n,U_n)(t) - I||_2 -> 0`
>
> holds as soon as
>
>   **(i)** `T ⊆ Rbar`, and **(ii)** `Nbar <= <<T>>_Pbar`.
>
> Given (i), condition (ii) is equivalent to: `Rbar/<<T>>` is **central** in
> `Pbar/<<T>>`, i.e. `Pbar/<<T>>` is a central extension of `Q`.

So the admissible lists are exactly those with `Nbar <= <<T>> <= Rbar`.  Three
consequences that change the extraction problem:

1. **`T` need not lie in `Nbar`.**  The whole commutator layer `[x, r]` is
   optional.  The largest legal target is `<<T>> = Rbar`, i.e. **`T` is just a
   finite set of defining relators for `Q` relative to the atlas**.  That
   replaces "present `U_Q = St_5(L)` and translate" by the strictly weaker
   "present `Q` on `A8 * A8`".  It is weaker by exactly one homological layer,
   `Rbar/Nbar = H_2(Q,Z)` (five-term sequence plus (23)).

2. **If one does want a list inside `Nbar`, it is now free.**

   > **Lemma (derived list).**  If `X` generates `Pbar` and
   > `Rbar = <<r_1,...,r_s>>_Pbar`, then
   > `Nbar = <<[x, r_i] : x in X, 1 <= i <= s>>_Pbar`, a list of size at most
   > `12 s`.
   >
   > *Proof.*  `<=` of the right side in `Nbar` is clear.  Put
   > `M = <<[x,r_i]>>`.  In `Pbar/M` each `rbar_i` is centralized by every
   > `x in X`, hence central, hence its normal closure is the subgroup it
   > generates.  So `Rbar/M = <rbar_1,...,rbar_s>` is central and
   > `[Pbar,Rbar] <= M`.  QED

   So there is **no search step** between a relative presentation of `Q` and a
   normal generating set of `Nbar`.  The only hard input is the presentation.

3. **The asymmetry between the two branches.**  To prove `Q`
   *nonhyperlinear* one needs a positive lower bound on the window energy for
   *some* finite `T ⊆ Rbar`; condition (ii) is irrelevant there, because only
   necessity is used.  Condition (ii) is needed only by the FALSE-side
   construction.  Every finite kernel window already enumerated is therefore
   already legitimate for the TRUE-side attack, and only the FALSE-side attack
   is blocked by the missing list.

4. **Why §4 chose `Nbar`.**  `Rbar` is finitely normally generated iff `Q` is
   finitely presented iff `H_2(Q,Z) = K_2(5,L)` is a finitely generated abelian
   group, which is not known.  `Nbar` is finitely normally generated
   unconditionally because `St_5(L)` is finitely presented (Krstic--McCool, as
   quoted at `notes/NOTEPAD.md:21608-21611`; **literature-transcription premise,
   not verified in repo**).  The usability criterion above keeps the
   unconditional target available while allowing anything up to `Rbar`.

---

## (b) Certification status of the enumerated collision words

### The engine: a finite-quotient obstruction

> **Lemma (no finite quotient).**  Let `V` be perfect with a central `Z <= V`
> and `V/Z` isomorphic to an infinite simple group.  Then `V` has no
> nontrivial finite quotient.
>
> *Proof.*  Let `M ⊴ V` with `V/M` finite.  The image of `M` in `V/Z` is
> normal, so trivial or everything.  If everything, `MZ = V` and
> `V/M ≅ Z/(Z ∩ M)` is abelian, hence trivial by perfectness.  If trivial,
> `M <= Z` and `V/M` surjects onto the infinite `V/Z`, contradiction.  QED

Applied with `V = Pbar/<<T>>` (perfect, since `A8 * A8` is perfect;
`Z = Rbar/<<T>>` central exactly when (ii) holds; `V/Z = Q` infinite simple,
`notes/NOTEPAD.md:21622-21628` via Preusser):

> **Screen.**  If some homomorphism `phi : Pbar -> F` onto a nontrivial
> **finite** group kills every word of `T ⊆ Rbar`, then `Nbar` is **not**
> contained in `<<T>>`, so `T` is unusable in the criterion.

Because `A8` is simple, each factor restriction of such a `phi` is trivial or
injective.  Both-trivial is vacuous; one-trivial gives exactly the canonical
retraction `(p_1,p_2) : A8 * A8 ->> A8 x A8` and its two coordinates;
both-injective with commuting images is a quotient of `A8 x A8` (Goursat);
both-injective with equal image is one of the `40320` automorphism folds
`x |-> x` on factor one, `x |-> g theta(x) g^{-1}` on factor two.

### Verdict on the enumerated windows

`experiments/atlas_relator_projection_screen.py` and
`experiments/atlas_relator_finite_quotient_screen.py` (new, this session) run
these screens on the complete spanning-tree windows of
`atlas_kernel_collision_enumerator.py`.  Results reproduced independently of
the committed artifact:

| half-radius `r` | complete kernel X-length | tree generators | X-lengths | nontrivial `(p_1,p_2)` | screen (D) |
|---:|---:|---:|:---|---:|:---|
| 2 | 4 | 20 | 4..4 | 0 | **FAILS** |
| 3 | 6 | 264 | 4..6 | 0 | **FAILS** |
| 4 | 8 | 2,734 | 4..8 | 0 | **FAILS** |
| 5 | 10 | 27,256 | 4..10 | 234 (X-length 9..10) | passes |

The radius-5 row reproduces `experiments/atlas-kernel-radius5-summary.json`
(`27022 + 234 = 27256`).  Screen (F), all `40320` automorphism folds, at
radius 2: **0 survivors** — independently confirming the exact minimax
statement of `experiments/atlas_kernel_collision_results.md` (ACW8).

> **Theorem (window-length lower bound).**  Every kernel element of `Rbar` of
> X-length at most `8` lies in `ker((p_1,p_2) : Pbar ->> A8 x A8)`, and there
> is a kernel element of X-length exactly `9` outside it.  Consequently, for
> every set `T` of kernel words of X-length at most `8`,
> `Nbar` is not contained in `<<T>>`; and **every usable relator list must
> contain a word of X-length at least 9.**

*Proof.*  Proposition 4 of `FALSE_RECURSIVE_ATLAS_EXHAUSTION.md:134-144` says
the radius-`r` spanning-tree set generates, as a subgroup, every kernel
element of X-length at most `2r`.  `(p_1,p_2)` is a homomorphism and kills
every one of the `2,734` radius-4 tree generators (computed), hence kills that
whole subgroup.  Sharpness is the radius-5 boundary word of X-length 9.  Then
apply the screen.  QED

**Consequences.**

* `Corollary 3` of `FALSE_RECURSIVE_ATLAS_EXHAUSTION.md:98-107` leaves the
  stopping point `L_0` unknown.  We now have `L_0 >= 9`, and the *cumulative*
  families `C_L` for `L <= 8` and `D_r` for `r <= 4` are all provably
  incomplete.  This is a **proof**, not evidence.
* The radius-2 constraint list (20 kernel words / 220 centrality constraints)
  which the repo calls "the first rigorous small target" is, as a candidate
  relator list, definitively insufficient — as are radius 3 and 4.  Their value
  as *necessary* constraints for the TRUE-side lower-bound attack is untouched
  (see (a)(3)).
* The earlier "no alignment satisfies all 220 constraints" scans did **not**
  cover this obstruction: those scans range over automorphism folds, in which
  both factor restrictions are injective.  The surviving map has one factor
  restriction *trivial*.  That degenerate sector is precisely what was missed.
* The 234 radius-5 boundary words are therefore not merely "the first
  tensor-flip obstruction": they are the **first words that can possibly
  belong to a usable list at all**.  Any usable list must include words with
  nontrivial factor projections, and by (TF4) of
  `atlas_kernel_collision_results.md` the 24 distinct projection pairs
  generate `H x H = GL_3(F2) x GL_3(F2)`, whose normal closure in `A8 x A8` is
  everything — which is why radius 5 passes screen (D).

**Verdict.** The 27,256 radius-5 tree words are *not certified*; they pass
every screen currently available (D and, a fortiori from radius 2, F) but no
positive certificate exists.  No amount of further enumeration can produce
one: enumeration only ever produces subgroups of `Rbar` and never an upper
bound on `Nbar`.  A certificate must come from the algebra side.  Note also
that of the 234 boundary words, 178 are certified **trivial in `U_Q`**
(`notes/FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md`), i.e. they lie in `Nbar` itself
and so contribute nothing to `<<T>> / Nbar`; the 56 survivors (4 cyclic
classes 11, 30, 44, 55) are the only ones that could represent nonzero classes
in `Rbar/Nbar = H_2(Q,Z)`.

---

## (c) Route design, and a second exact pilot

### Pilot 2: the chart overlap is trivial

`experiments/atlas_relator_chart_overlap.py` (new) computes, by exact
`F2`/prefix arithmetic, the two 16-dimensional chart algebras
`A_i = span{delta_u delta_v^* : u,v in D_i}` inside `L` for
`D_1 = (01, 1, 000, 001)`, `D_2 = (00, 1, 010, 011)`
(`experiments/atlas_two_chart_search.py:26-31`), expands both to a common
per-degree right-path depth, and intersects.

```
dim A1 = dim A2 = 16,   dim (A1 cap A2) = 3,   |K1 cap K2| = 1
```

So **the two atlas charts intersect trivially in `Q`**.  Consequences:

* `K1 *_{K1 cap K2} K2 = K1 * K2 = Pbar`: there is **no amalgam layer**.  None
  of `Rbar` comes from chart overlap, so the standard "identify the common
  subgroup" route to a relative presentation yields nothing at all.  Every
  relator is a genuine mixed-chart Steinberg relation of the shape (6)-(7).
* `Rbar` meets every conjugate of every factor trivially, so `Rbar` acts freely
  on the Bass--Serre tree of `Pbar` and **`Rbar` is a free group** (of infinite
  rank).  Equivalently `Rbar = pi_1(Gamma)` for the coset graph `Gamma` with
  vertices `Q/K_1 ⊔ Q/K_2` and edge set `Q`.  Normal generation of `Rbar` in
  `Pbar` is exactly "`pi_1(Gamma)` is generated by finitely many `Q`-orbits of
  cycles"; the shortest cycles have syllable length 4 and are the 20
  cross-chart commutators of radius 2.

### The route I recommend

The `notes/EXPLICIT_LEAVITT_ATLAS.md:227-238` two-step program is right, but
(a) simplifies its justification and removes one of its two hard steps.

**Step 0 (free, from (a)).**  Do not aim at `Nbar`.  Aim at any `T` with
`Nbar <= <<T>> <= Rbar`.  In particular the following suffices and is what the
Steinberg route naturally produces:

> Let `T_St` be a finite relator set with `Pbar/<<T_St>> ≅ St_5(L)` compatibly
> over `Q`.  Then `Rbar/<<T_St>> ≅ K_2(5,L)`, which is **central** in
> `St_5(L)` for `n >= 5` (Kervaire--Steinberg; `notes/NOTEPAD.md:21650-21652`).
> Hence `Nbar <= <<T_St>>` automatically, and `T_St` is usable.

This is worth stating explicitly because it means the extraction **never needs
`U_Q ≅ St_5(L)`, never needs `K_2(5,L) = 0`, and never needs `K_2(5,L)`
finitely generated**.  Only centrality is used.

**Step 1.**  Fix a five-leaf prefix code and its `Theta`-isomorphism
`M_5(L) ≅ L`, giving `E_5(L) ≅ Q` and the 100 generators
`x_ij(a) = 1 + gamma_i a gamma_j^*`, `i != j` in `{1..5}`, `a in {1,e,f,e^*,f^*}`.
Warning found here: the common refinement `E = {000,001,010,011,1}` of
`D_1, D_2` is **not** usable as that code — refinement must be *uniform*
(`notes/EXPLICIT_LEAVITT_ATLAS.md:104-118`, the `m(alpha) = m(beta)` rank
condition), and `E` refines `D_1` with multiplicities `(1,1,2,1)`.  This is the
same fact as `|K1 cap K2| = 1`.  The uniform refinements of `D_i` have
`4 * 2^k` leaves, so the natural superperfect hosts are
`G_i = GL_8(F2) ⊃ K_i`, and a rank-5 chart has to be chosen independently of
both.

**Step 2 (the real work).**  Express each `x_ij(a)` as an explicit word in
`X`.  For the rank-3 code this is exactly (7) of
`notes/EXPLICIT_LEAVITT_ATLAS.md:139-151`; the rank-5 analogue has to be
written out.  This is a factorization problem in `Q` over the atlas, and it is
the step to spend effort on.

**Step 3.**  Write the finite Steinberg presentation of `St_5(L)` over the
finite ring presentation
`L = F2<e,f,e^*,f^*> / (e^*e = f^*f = 1, e^*f = f^*e = 0, ee^* + ff^* = 1)`,
and translate every relator through Step 2.  Output `T_St`.

**Step 4 (cheap validation, mandatory).**  Run screens (D) and (F) on the
output.  Any output list failing them is wrong.

### The next computation (not run here)

Extend screen (D)/(F) to the only uncovered family: finite `F` generated by
**two non-commuting injective copies of `A8`** with `F` not isomorphic to
`A8`.  By Goursat, everything else is already covered.  Candidates:
`A9, S8, A10, GL_5(2), Sp_6(2), M_24`.  The screen is cheap in the right
coordinates: the 20 radius-2 words are cross-chart commutators `[y_2, x_1]`, so
a pair `(alpha, beta)` survives them only if `beta(y) in C_F(alpha(x))` for all
20 pairs — an intersection of centralizers, computed once per `F`, which cuts
the search before any word evaluation.  Survivors are then tested against the
radius-5 list.  This is a short GAP job (MSI, normal partition; avoid
`acn112/acn116`).  A survivor would push the lower bound on `L_0` past 10; no
survivor is one more passed screen for the radius-5 window.

---

## (d) Candidate claim statements for the graph

Proposed, not written (research/ is read-only for this session).

1. **`atlas-relator-list-central-sufficiency`** (claim, provable now).
   *Let `Pbar = A8 * A8 ->> Q`, `Rbar = ker`, `Nbar = [Pbar,Rbar]`.  For finite
   `T ⊆ Rbar` with `Nbar <= <<T>>_Pbar`, the canonical regular-`A8` criterion
   of `notes/EXPLICIT_LEAVITT_ATLAS.md` §9 holds verbatim with `Sbar` replaced
   by `T`.  Equivalently, the admissible relator lists are exactly those with
   `Nbar <= <<T>> <= Rbar`, i.e. those for which `Pbar/<<T>>` is a central
   extension of `Q`.*
   Invalidates the framing that a normal generating set of `Nbar` is required.

2. **`atlas-relator-window-length-nine-lower-bound`** (claim, proved above).
   *Every kernel word of X-length at most 8 lies in the kernel of the
   retraction `A8 * A8 ->> A8 x A8`.  Hence no set of kernel words of X-length
   at most 8 normally generates a subgroup containing `[Pbar,Rbar]`, and the
   stopping point `L_0` of `FALSE_RECURSIVE_ATLAS_EXHAUSTION.md` Corollary 3
   satisfies `L_0 >= 9`.  The bound is sharp at the enumerated boundary: a
   kernel word of X-length 9 with nontrivial factor projections exists.*

3. **`atlas-two-chart-overlap-trivial`** (claim, computed exactly).
   *`K1 cap K2 = 1` in `Q`, while the two 16-dimensional chart algebras meet in
   dimension 3.  Hence the atlas source is the unamalgamated free product,
   `Rbar` is a free group, and no relator of the atlas comes from chart
   overlap.*

4. **`atlas-relator-steinberg-rank-five-translation`** (route, open).
   The Step 1-3 program above, whose only nontrivial input is Step 2 and whose
   correctness needs only centrality of `K_2(5,L)` in `St_5(L)`.

---

## Files produced

* `experiments/atlas_relator_projection_screen.py`
* `experiments/atlas_relator_finite_quotient_screen.py`
* `experiments/atlas_relator_chart_overlap.py`
* this note

Reproduce with
`python3 experiments/atlas_relator_finite_quotient_screen.py --radius 2 --fold-screen`
(seconds), `--radius 4` (seconds), `--radius 5` (about two minutes), and
`python3 experiments/atlas_relator_chart_overlap.py` (seconds).
