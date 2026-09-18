# Can the BBMZ hyperbolic-groups method reach hierarchically hyperbolic groups?

Lane `bh-hhg`, BH swarm, 2026-09-18. Source read: Belk--Bleak--Matucci--Zaremsky,
*Hyperbolic groups satisfy the Boone--Higman conjecture*, arXiv:2309.06224v3,
e-print TeX `hyperbolic_boone_higman.tex`, fetched on MSI into
`gqsrc/bh-hhg/x/`. Labels below are the TeX labels.

## 0. Answer in brief

- **Not for HHGs with flats, as the method stands.** The method needs a Cantor
  action by a rational similarity group (RSG) with finite nucleus. In such a group
  every group of germs at a rational point is virtually infinite cyclic
  (`prop:CyclicStabilizers`). Natural boundaries of groups with flats have points
  fixed by `Z^2` with faithful germs. BBMZ flag exactly this in their open-questions
  paragraph ("the group of germs at any point must be virtually cyclic ... an
  impediment for several potential approaches").
- **Landed.**
  - `finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs` (ESTABLISHED, lane
    proof): a free abelian group fixing a rational point acts through germs of rank
    at most one. A consequence: germ-faithful `Z^r`-fixed points (`r ≥ 2`) of any
    boundary model must be coded irrationally.
  - `z2-free-z-embeds-in-a-finite-nucleus-rsg` (OPEN): the sharp host-class test.
    `Z^2 * Z` lies in every closed-surface mapping class group (Koberda) and is
    hyperbolic relative to `Z^2`. `V` already fails to contain it
    (Bleak--Salazar-Díaz). A negative answer would put the closed-surface mapping
    class groups, and every group containing `Z^2 * Z`, out of reach of the whole
    BBMZ host class.
- **No positive result for a named HHG subclass.** The HHGs already known to
  satisfy Boone--Higman on main (hyperbolic groups, RAAGs and virtually special
  cubulated groups via linearity, punctured-surface mapping class groups via BFFHZ)
  are all reached by other methods.

## 1. The BBMZ pipeline

1. **Tree of atoms.** `∂_h G`, for a word metric, is the end space of the tree of
   atoms (BBM Thm 3.6, restated in `ssec:horofunction`). This holds for every group.
2. **Finitely many types.** `prop:fin_many_types` (BBM Cor 3.28): hyperbolic `G`
   has finitely many types of atoms. This gives the type graph `Γ` and a system of
   addresses `C_v → ∂_h G`. BBMZ remark that `Z^2` also has finitely many types.
3. **Rationality.** `thrm:BBM` (BBM): for hyperbolic `G` with `∂_h G` having no
   isolated points, the action on addresses is rational.
4. **RSG.** `prop:hyp_similarities`: under 2–3 the image is an RSG. This needs only
   finitely many types plus rationality, not hyperbolicity.
5. **Free product trick.** `thrm:FreeProductBoundary`: for `G * Z` the boundary has
   no isolated points and the action is faithful, for any nontrivial `G`.
6. **Contracting.** `lem:contractinglemma` (the constant `18δ+6`) and
   `thrm:contracting`: finite nucleus. This is where δ-hyperbolicity is used in an
   essential, uniform way. The local action at a deep atom depends only on a
   bounded configuration near it.
7. **Host.** `thrm:rsg_to_simple`, `prop:contr_to_simple`: full contracting RSGs
   embed in finitely presented simple groups. The proof goes through Zaremsky's
   `thrm:action_to_simple` (oligomorphic action with finitely generated stabilizers),
   `prop:HighlyTransitiveAction`, `prop:CyclicStabilizers` and
   `prop:fin_gen_stabs`.

Steps 1, 4, 5 and 7 are general. Steps 2, 3 and 6 use hyperbolicity. For groups
with flats the obstruction below sits at step 6, or already at step 7's
`prop:CyclicStabilizers`, which the host class forces.

## 2. The germ constraint

`prop:CyclicStabilizers`: for an RSG with finite nucleus and a rational point `ω`,
`[G]_ω` is virtually infinite cyclic. The landed lemma is the abelian corollary.
If `Z^r` fixes `ω`, at least `r − 1` independent directions of it are the identity
near `ω`.

**`Z^2` horofunction corner.** BBMZ `ex:Z2`: for `{(1,0),(0,1)}`,
`∂_h Z^2 ≅ \hat Z^2 \ Z^2`, where the point `(+∞, n)` is the horofunction
`(x,y) ↦ −x + |y−n|`. Translation by `(m,n)` acts coordinatewise and fixes the
four corners. Near `(+∞,+∞)` the points `(k,+∞)` (k large) and `(+∞,k)` (k large)
accumulate, and they are moved by `m` and `n` respectively. So `Z^2 → [Z^2]_corner`
is injective.
- In any coding in which a group containing this configuration equivariantly acts
  as a finite-nucleus RSG, the corner must go to an irrational point.
- Caveat: `∂_h Z^2` has isolated points, for example `(k,+∞)`, so it is not itself
  a clopen subset of an irreducible shift of finite type. The corner phenomenon
  persists wherever a flat's boundary sits inside a larger Cantor boundary; this is
  a heuristic.

**Mapping class groups (heuristic).** Twists `T_a, T_b` about disjoint curves fix
`[a] ∈ PML`. For `μ` meeting `a`, `T_a^m(a + εμ) ≈ (1 + ε m i(a,μ)) a + εμ` is
projectively different from `a + εμ`, and `T_b` moves laminations meeting `b`. So
the germs are faithful at `[a]`. `PML` is a sphere, so this constrains only Cantor
models that map equivariantly onto it and are germ-faithful at lifts of `[a]`.

## 3. Why `2V`-type product models fail the nucleus

`Z^2 * Z` lies in Brin--Thompson `2V`: every RAAG embeds in `2V`
(`every-raag-embeds-in-brin-thompson-group-2v`). The natural model has `a = (f, id)`
and `b = (id, f)` with `f ∈ V` north--south.
- **Interleaving coding.** Under the coding `x_0 y_0 x_1 y_1 …`, a prefix
  replacement of length change `d` in the `x` stream shifts `x` against `y` by `d`
  letters.
- **The local action.** At deep cones it is a "delay-`d`" transducer.
- **Unbounded delays.** Near its attractor, `f^k` changes prefix lengths by an
  amount growing linearly in `k`. So `⟨a⟩` alone has delay-`d` local actions
  occurring infinitely often for unboundedly many `d`, and the nucleus is infinite.
- **Consistency.** This matches the germ lemma: `(p,p)`, with `p` the attractor of
  `f`, is a rational point fixed by `Z^2` with faithful germs.

This is a sketch for one coding; it is not a claim about `2V` in general.

## 4. Equicontinuous directions (sketch)

Let `a` act on a binary cone `C_v` as the binary odometer `x ↦ x + 1` on `Z_2`,
and let `b` commute with `a` on `C_v`.
- **Centralizer.** A homeomorphism commuting with a minimal equicontinuous map is
  determined by the image `θ` of one point, and on the dense orbit it is `x ↦ x + θ`.
  So `b|_{C_v}` is translation by some `θ ∈ Z_2`.
- **Rationality.** If `b` is a rational homeomorphism, its local actions at the
  cones `C_{v w}` are translations by the "tails" of `θ + w`. There are finitely
  many exactly when the 2-adic expansion of `θ` is eventually periodic, that is,
  `θ ∈ Z_(2) = Q ∩ Z_2`.
- **Rank bound.** `⟨1, θ⟩ ≤ Q` has rank `1`. So `⟨a, b⟩` restricted to `C_v` has
  rank at most `1`.

This case alone doesn't rule out `Z^2 * Z`. It says that equicontinuous behaviour,
the kind a nucleus allows beyond `V`, cannot supply a rank-two free action either.

## 5. The missing input and the open questions

- **The dynamics a negative answer needs.** Bleak--Salazar-Díaz exclude
  `Z^2 * Z ≤ V` using revealing pairs, i.e. the dynamics of single elements of
  `V`. A negative answer to `z2-free-z-embeds-in-a-finite-nucleus-rsg` needs the
  analogue for a finite-nucleus RSG. Each element should split into
  - a finite-order clopen part,
  - equicontinuous parts on cones, controlled as in §4, and
  - an attracting--repelling part with finitely many rational periodic points,
    controlled by §2.

  With that, the BSD mechanism (a `Z^2` whose directions are locally rank one
  cannot be ping-ponged against `c`) would plausibly transfer.
- **What a positive answer needs.** A `Z^2` that is demonstrative in the
  Bleak--Salazar-Díaz sense: an open set whose `Z^2`-translates are pairwise
  disjoint, inside some finite-nucleus RSG. §2 and §4 say its accumulation points
  must be irrational or its directions must be locally rank one.
- **Also open.**
  1. Does some closed-surface mapping class group act on a Cantor space as an RSG
     at all, with or without finite nucleus?
  2. Is there a variant of step 6 that tolerates germ groups of higher rank at
     rational points, i.e. hosts that are finitely presented but not contracting?
     BBMZ `quest:all_fp_subgroups_of_rat` is the rational-group form of this.

## 6. Not done

- No reading of Belk--Bleak--Matucci (arXiv:1711.08369) beyond BBMZ's restatements.
- No search of the HHS-boundary literature for Cantor models.
- Nothing on extra-large-type Artin groups, which are HHGs by Hagen--Martin--Sisto.
  Artin-group BH is carried by `artin-groups-satisfy-boone-higman` and its
  neighbors.
