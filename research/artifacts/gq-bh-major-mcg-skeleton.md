# Closed mapping class groups (BBMZ 5.3(2)): end-to-end proof skeleton

Owner: bh-major-mcg (team lead), 2026-09-18. This is the live version of
`board/major-mcg.md`. Every item is a lane result unless marked as literature, and
none is independently reviewed.

## Target

Every closed-surface mapping class group `Mod(S_g)`, `g ≥ 3`, embeds in a finitely
presented simple group. By `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`,
it is enough to have a finitely presented, full, clopen-transitive Cantor group that
contains `Mod(S_g)`, or a finite-index subgroup of it.

## The obstruction every route must respect: rank of flats

- Commuting Dehn twists on disjoint curves generate `Z^k` with `k` up to `3g − 3`, and
  Koberda's twist powers generate `Z² ∗ Z`.
- Rank-one hosts cannot carry this. `perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts`
  (bh-free-51) shows perfect subsurface groups are locally trivial in abelian-germ hosts
  (`V`, `nV`, germ extensions of `V`, normal-form hosts). So the host needs nonabelian
  point germs at curve points `[d] ∈ PML`.
- Continuous normal forms fail for the same reason (`deligne-forms-are-singular-on-commuting-parabolic-diagonals`).

## Routes

| Route | Host | What is done | Open gate | Owners |
|---|---|---|---|---|
| R1 | `𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]`, `m = 6g−7` | embedding, full, clopen transitive; `𝒯_1` fp; × Cuntz is simple and acyclic | finite presentation of `𝒯_m` for `m ≥ 2`, via the edge-split operad: Ore condition plus finite spine (`edge-split-operad-satisfies-ore`), then saturation | bh-free-54, bh-free-61, bh-g3-steinfarley |
| R2 | train-track split host (`train-track-trace-groupoid-hosts-closed-mcg`) | right-LCM cylinder family (`train-track-split-cones-have-least-common-descendants`); Serret gate on minimal suited laminations (Agol, Penner–Harer) | G1 at non-generic laminations together with G2 (regularization); Li's (F) and (t<d) | bh-major-mcg |
| R3 | Bishop–Schesler branch hosts (`efrf-groups-frattini-embed-in-efrf-branch-groups`) | `Mod(S_g)` is fp and RF, hence effectively RF, so it embeds in their branch groups | a finitely presented simple host for those branch groups | bh-major-branch-a/b |
| R4 | exploded rank-one actions | dead: twist data cannot be localized (bh-free-51) | none | none |
| R5 | `2V_Λ(n)` (Deligne analogue) | simple, acyclic; the finite-dissection-type engine is dead at `n = 2` | not needed for MCG; shares the non-LCM lesson | bh-free-55 |

## Why R1 and R2 are complementary

- **R1** has the whole `GL`-germ groupoid, so every mapping class is automatically a
  finite cylinder exchange: its Serret gate is free. The price is that the ambient
  dissection operad is too big (non-unique minimal common refinements, prime dissections
  at unboundedly many sizes). Finiteness must come from a cofinal suboperad (edge splits)
  that satisfies the Ore condition.
- **R2** uses only the moves `Mod` itself generates. Least common descendants hold
  automatically, and the local rank is the number of large branches. The price is the
  Serret gate at non-generic laminations.
- **Possible merger:** does the edge-split suboperad of R1, restricted to train-track
  cones, recover R2's split family? Train-track cones are rational polyhedral cones, and
  splits are single hyperplane cuts. If edge splits refine every split cone, R1's
  finiteness would also finish R2's G4. Not checked.

## R2 gate list, precise

1. **G1(generic): done** (literature, read at source). Minimal suited laminations have
   common splittings: Agol, Corollary `spliteq`, and Penner–Harer 2.3.1.
2. **G1(non-generic) + G2: open.** Needed:
   - a Cantor unit space `Ω` containing the partial traces, i.e. laminations that are
     not filling or not uniquely ergodic;
   - on it, every `f ∈ Mod` acting by finitely many cylinder exchanges.
   Proposed design: take `Ω` to be the space of ends of the directed system of all
   complete tracks under split descendance. `Mod` then acts on it canonically, and the
   gate becomes compactness plus a finite standard atlas. Test: germ groups at `[d]` must
   be nonabelian.
3. **G3: expected free** after Cuntz stabilization (bh-lattices' comparison lemma), once
   the category is in Li's form.
4. **G4: half done.** Right-LCM, finitely many objects and a finite Garside family are
   proved. Li's (F) and (t<d) are open. Agol's periodic maximal splitting sequences are
   the natural source of the multiplicity in (t<d).

## Lesson for general BH

Hosts for groups with higher-rank flats should be built from the group's own
commuting local moves. Two local properties then give least common descendants: moves
with disjoint supports commute, and the wall deciding a move is unchanged by moves
elsewhere. The number of independent moves gives variable local rank. What remains is
always a Serret gate at non-generic points, where the group's moves stop being
canonical.
