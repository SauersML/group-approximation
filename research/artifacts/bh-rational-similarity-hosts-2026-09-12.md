# Rational similarity groups as Boone--Higman hosts: where the Kazhdan transfixing argument breaks

Lane `bh-rational-similarity-hosts`, 2026-09-12.

## 0. Question and answer in brief

The Rover--Nekrashevych route died because a subgroup with property (T) of
`V_d(H)` virtually embeds in a finite power of the self-similar group `H`
(`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`). This note runs the
same argument inside rational similarity groups (RSGs), the hosts of
Belk--Bleak--Matucci--Zaremsky arXiv:2309.06224, and records exactly where it
stops.

- **The argument survives in general form.** Replace the full shift by a finite
  graph of cone types and the self-similar group by any eventually self-similar
  groupoid `H` of cone homeomorphisms. FW subgroups of a group whose elements
  send deep cones onto cones with local actions in `H` virtually embed in a finite
  product of vertex groups of `H`
  (`fw-subgroups-of-eventually-similar-groups-virtually-embed`).
- **Two special cases give residual finiteness or finiteness.** Trivial local
  actions force finite FW subgroups. Synchronous local actions force residually
  finite FW subgroups.
- **So a non-residually-finite Kazhdan group can sit in such a host only through
  a local groupoid whose vertex groups are not residually finite.** Section 3
  compares this with the actual definitions of RSGs.

## 1. What is already settled on main about universal RSG hosts

"Every decidable group embeds in an RSG" is already false, for two independent
reasons:

- `complexity-bounded-host-classes-are-not-universal`: finitely generated groups
  of rational homeomorphisms have single-exponential word problem
  (`rational-homeomorphism-subgroups-have-exponential-wp`), so some two-generated
  decidable group embeds in none of them.
- `decidable-fp-groups-need-not-embed-in-rational-group`: a finitely presented,
  residually finite, solvable decidable group admits no rational Cantor
  embedding at all.

Both exclusions are about word-problem complexity or solvable structure. Neither
is known to apply to Deligne's lattice, which is finitely presented, has solvable
word problem, has property (T), and is not residually finite. Whether such an
input embeds in a rational similarity group is the question this lane adds.

## 2. The general transfixing theorem

Statement and proof: `fw-subgroups-of-eventually-similar-groups-virtually-embed`
and `fw-eventually-similar-virtual-embedding-proof`.

The argument uses three things about the host, and nothing else:

1. **Cone to cone.** Each element sends all but finitely many cones onto cones.
2. **Local actions in a groupoid.** The resulting local actions
   `beta_v^-1 o f o beta_u` lie in one groupoid `H`, which is closed under
   restriction to deep cones.
3. **Residual finiteness of the vertex groups of `H`.** Needed only for the
   residual finiteness conclusion, not for the embedding.

For `V_d(H)` all three hold with `H` a group of tree automorphisms.

## 3. Rational similarity groups: definitions from the source

Read on 2026-09-12 from the arXiv TeX source of arXiv:2309.06224v3,
`hyperbolic_boone_higman.tex`, on MSI. Line numbers refer to that file.

- **RSG (line 637).** "A subgroup `G ≤ R_{Γ,E}` will be called a rational
  similarity group (RSG) if, for every pair of cones `C_α, C_β ⊊ E` with
  `t(α)=t(β)`, there exists `g∈G` that maps `C_α` to `C_β` by the canonical
  similarity." Here `R_{Γ,E}` is the group of rational homeomorphisms of the clopen
  set `E` in the shift of finite type `Σ_Γ`.
- **Local action (line 335).** For a nondegenerate map `f` and a cone `α`, "the
  local action of `f` at `α` is the map `f|_α: C_{t(α)} → C_{t(f̄(α))}`", defined
  through canonical similarities `L_α` and `L_{f̄(α)}`. A map is rational if it has
  only finitely many distinct local actions (line 363).
- **Nucleus and contracting (lines 691--695).** "The nucleus of `f` ... is the set
  of all local actions that occur infinitely often." The nucleus of `G` is the
  union over `g ∈ G`, "the smallest set of maps such that for all `g∈G` we have
  `g|_α∈Nuc_G` for all but finitely many `α`." `G` is contracting if `Σ_Γ` has an
  irreducible core and `Nuc_G` is finite.
- **`f̄(α)` (TeX section `ssec:rational`).** "`C_β` is the smallest cone in `Σ_Γ`
  that contains `f(C_α)`", and `f(α·ω) = f̄(α)·f|_α(ω)`.
- **Nucleus of injections (`def` before `prop:NucleusHasProperties`).**
  - LocNuc: "For each `p∈Nuc`, every local action `p|_α` belongs to `Nuc`."
  - InvNuc: "Each `p∈Nuc` is an injective open map, and satisfies
    `Nuc_{p^{-1}}⊆Nuc`."
  - ProdNuc: "If `p: C_v→C_w` and `q: C_u→C_v` are elements of `Nuc`, then
    `Nuc_{pq}⊆Nuc`."
  - Line 736: the nucleus of an RSG over a shift with irreducible core is a nucleus
    of injections. Line 761: LocNuc and InvNuc hold for every subgroup.
- **Characterization (`thrm:RSGCharacterization`).** Over an irreducible core,
  `{f∈R_{Γ,E} | Nuc_f⊆Nuc}` is a full RSG with nucleus `Nuc`, and every full RSG has
  this form.
- **Nuclear elements need not be invertible (line 844).** In proving finite
  presentation: "the elements of `Nuc` might not even be invertible."
- **RN groups are special RSGs (line 657).** `V_n(G)` for a finite-state
  self-similar `G` "is a full RSG".
- **Germs (line 1794).** "Let `G≤R_{Γ,E}` be an RSG with a finite nucleus, and let
  `ω∈E` be a rational point. Then the group of germs `[G]_ω` is virtually infinite
  cyclic."

## 4. Where the transfixing argument breaks for RSGs

Let `S` be an RSG and `g ∈ S`. For all but finitely many cones `α`, `g|_α` lies in
`Nuc_S`, and `g(C_α) = f̄(α) · im(g|_α)`.

1. **Break point: non-surjective nuclear elements.** If some `p ∈ Nuc_S` is not
   surjective onto its target cone space, then `g(C_α)` is a proper clopen subset of
   the cone `C_{ḡ(α)}` for infinitely many `α`, and not a cone.
   - Then `g.[beta_α]` leaves the cone markings `M` for infinitely many `α`, so `M`
     is not commensurated.
   - The first hypothesis of Section 2 (cone to cone) fails, and there is no
     residually finite group of local maps to project to.
   - Line 844 shows that BBMZ allow exactly this.
2. **Surjective nuclei over the full shift give nothing new.**
   - Let `Γ` have one node with `d` loops, and suppose every nuclear element is
     surjective. For `p ∈ Nuc_S`, the images `p(C_x)` of the `d` child cones are
     cones partitioning the whole space, because each `p|_x` is again nuclear and
     surjective.
   - A complete prefix code of size `d` in the `d`-ary tree is the set of letters.
     So `p` permutes the children, and by induction `p` is a tree automorphism.
   - The nucleus then generates a self-similar group `H`, every element of `S` has
     a cone partition with images cones and local actions in `H`, and
     `S ≤ V_d(H)`. The Rover--Nekrashevych theorem already applies.
3. **Surjective, length-changing nuclei over other shifts.** Assume every node has
   out-degree at least two, which Section 2 uses.
   - Cone to cone holds. By LocNuc every nuclear map sends every cone onto a cone.
     By InvNuc and ProdNuc, inverses and composites of nuclear maps have nuclear
     local actions on deep cones. So the maps generated by the nucleus form an
     eventually self-similar groupoid.
   - Section 2 then gives a virtual embedding of FW subgroups into vertex groups of
     that groupoid.
   - Residual finiteness then needs those vertex groups to be residually finite.
     The synchronous criterion (part 3 of the claim) does not apply when nuclear
     maps change path length.

So the argument stops at non-invertible or length-changing nuclear maps. Section 5
shows that this is not a technical defect of the method.

## 5. The barrier: Gromov's question

`rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf`, via
`rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf-proof`:

- If some hyperbolic group is not residually finite, Kapovich--Wise and an
  Olshanskii common quotient with a torsion-free hyperbolic Kazhdan partner give an
  infinite hyperbolic Kazhdan group `Q` with no finite quotients. This repeats
  Section 4 of `hyperbolic-quotientless-kazhdan-proof-2026-09-11.md`.
- `Q` embeds in a full, contracting RSG by `thrm:hyp_to_contracting`.
- So "every Kazhdan subgroup of every contracting RSG is residually finite" implies
  that every hyperbolic group is residually finite.

Consequences:

- The Rover--Nekrashevych obstruction cannot be extended to contracting RSGs
  without settling `non-residually-finite-hyperbolic-group`. Any such extension
  must fail at the break points of Section 4, or else be a proof of Gromov's
  conjecture.
- If a non-residually-finite hyperbolic group exists, its common-quotient Kazhdan
  group `Q` sits in a contracting RSG whose nucleus contains a non-surjective or
  length-changing element. By Section 4.2 that RSG does not lie over the full shift
  with a surjective nucleus.

## 6. Status of the lane questions

- **Q1 (where it breaks).** Answered by Section 4: non-surjective nuclear maps,
  which BBMZ explicitly allow; and length-changing surjective nuclear maps on
  shifts that are not full shifts.
- **Q2 (can RSGs host non-RF Kazhdan groups such as Deligne's lattice).** Not
  decided.
  - A universal negative answer for contracting RSGs would prove every hyperbolic
    group residually finite (Section 5). A negative answer for Deligne's lattice
    must therefore use something specific to it, for example its infinite centre.
  - One attempt, recorded and not landed. Let `K ≤ S` have (T), `S` finite-nucleus,
    and `z ∈ Z(K)` of infinite order. If `ω` is a rational point that is an
    attracting periodic point of a power of `z` and has finite `K`-orbit, then a
    finite-index subgroup of `K` fixes `ω`. Its germ image in the virtually cyclic `[S]_ω` (line 1794) is finite, and
    a power of `z` would have trivial germ at `ω`, which is impossible.
  - That excludes attracting points with finite `K`-orbits. It does not exclude
    infinitely many attracting points, or odometer-like central elements with none,
    so it does not decide Q2.
  - A positive answer needs a rational, finite-nucleus action of `Sp_4(Z)`-by-`Z`
    on a shift of finite type in which all point germs are virtually cyclic. No such
    action is known here.
- **Q3 (bearing on Gromov).** The barrier claim above. It gives no counterexample;
  it says where one would have to live.

No claim here is proved in Lean. No novelty is claimed for the commensurated-set
method (Cornulier) or for the BBMZ material.
