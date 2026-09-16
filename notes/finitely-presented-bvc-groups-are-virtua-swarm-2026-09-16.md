# Swarm lane: finitely-presented-bvc-groups-are-virtually-cyclic (2026-09-16)

Target: `finitely-presented-bvc-groups-are-virtually-cyclic` (von Puttkamer–Wu Conjecture B,
arXiv:1607.03790). Lock held as `swarm-finitely-presented-bvc-groups-`. Nothing committed.

## Setup

Landed inputs used:

- `bvc-amalgams-have-two-transitive-vertex-actions` (+ `-proof`, requires []): a BVC amalgam
  `A *_C B` has `|C\A/C| = |C\B/C| = 2`. Its Step 3 bounds the conjugacy classes with a given
  cyclically reduced length `l >= 2`, uniformly in `l`.
- `non-ascending-hnn-extensions-lack-bvc` (vPW Lemma 2.4 import).
- `virtually-solvable-bvc-groups-are-virtually-cyclic` (vPW Proposition 1.12 import).
- `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension` (landed, route with requirements).

## What was proved

**Theorem** (`bvc-groups-splitting-over-vc-subgroups-are-vc`; proof route `-proof`; full proof in
`research/artifacts/bvc-vc-splittings-2026-09-16.md`). Let `G` have BVC and split nontrivially
over a virtually cyclic subgroup `C`, as an amalgam with `C` proper in both factors or as an HNN
extension. Then `C` is finite and `G` is virtually cyclic. In the amalgam case
`[A:C] = [B:C] = 2`; in the HNN case `C = C' = H`. No finite generation is assumed. check.sh
reports the claim as established.

Key new ingredients:

1. *Property P.* "Every element is conjugate into one of finitely many VC subgroups." It follows
   from BVC and passes to quotients. Step 3 of the landed amalgam route works verbatim under P.
2. *Rigidity of length-two products* (artifact Lemma 2). `ab ~ ab'` forces
   `b' = (a^{-1}ca) b c^{-1}` with `c` in `C ∩ aCa^{-1}`. So if `C ∩ aCa^{-1}` is finite for one
   `a`, the other factor is finite (Proposition 3). Minasyan–Osin study this weakly malnormal
   situation; the conclusion here is elementary.
3. *Counting modulo a normal cyclic subgroup.* With `C` infinite VC of finite index in VC factors,
   `<z^{R_A R_B}>` is normal in `G`. The quotient is an amalgam of finite groups with property P,
   and it has at least `((p-1)(q-1))^m / m` classes of length `2m`. So `p = q = 2`.
4. *Virtual solvability.*
   - `G/C ≅ D_∞` with `C` infinite is virtually solvable.
   - An ascending HNN extension of an infinite VC group is finite-by-solvable. The maximal finite
     normal subgroups of the copies `t^{-k}Ht^k` coincide, and the infinite-order elements of the
     kernel modulo that subgroup form an abelian normal subgroup of index at most 2.

**Reduction** (`fp-bvc-vc-via-excluding-vc-splittings`). The target follows from the theorem and
the new hole `fp-bvc-groups-without-vc-splittings-are-finite`: a finitely presented BVC group
with no one-edge splitting over a VC subgroup is finite. Given the theorem the hole is
equivalent to the target, so this relocates the difficulty rather than reducing it. It records
that every remaining counterexample is infinite without such a splitting (one-ended, by
Stallings' theorem quoted from memory).

**Corollary** (recorded in the claim). If a finitely presented non-VC BVC group maps onto `Z`, the
ascending base `H` from `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension` is not VC.

## Honest novelty assessment

For finitely generated `G` each case plausibly follows from the literature. This is from memory
and was NOT verified this session:

- `C` finite: virtually free, hence hyperbolic (vPW Corollary 3.3(a)).
- Some `C ∩ aCa^{-1}` finite: Minasyan–Osin acylindrical hyperbolicity of tree actions, with vPW
  Proposition 3.2.
- VC factors: virtually `Z × F_n`, hence linear (vPW arXiv:1704.05304 Theorem I).
- Ascending HNN over a VC base: virtually solvable.

What this lane adds is a uniform elementary proof inside the repo graph that needs no finite
generation. It covers, for example, non-finitely-generated amalgams over `Z`.

*Correction by the referee (2026-09-16).* This assessment was too generous. Minasyan–Osin
Corollary 2.2 (arXiv:1310.6289; already imported as `fpbs-minasyan-osin-weakly-malnormal-splittings`)
needs no finite generation. Combined with von Puttkamer–Wu Proposition 3.2 and Corollary 3.4,
applied to `G` and to `G/Z`, and with Proposition 1.12, it yields the whole theorem without
finite generation. The theorem is therefore not new. Only the elementary counting proof is
new. See artifact §5.

## Approaches and where each dies

1. *Sharply 2-transitive vertex actions with point stabilizer `Z`* (explored earlier this
   session, before the rigidity lemma).
   - A torsion-free BVC amalgam over `C = Z` with trivial two-point stabilizers would need a
     sharply 2-transitive action with point stabilizer `Z`. That leads to a Zech-logarithm-type
     function `f: Z - 0 -> Z - 0` with `f(f(m)+n) = f(n) + f(m + f(-f(n)))`.
   - The split (near-field) case was excluded by an `F_2[z^{±1}]`-module argument. The non-split
     case was not settled.
   - Superseded: Proposition 3 of the artifact makes trivial two-point stabilizers force finite
     factors, with no classification needed.
2. *Extending the counting to non-VC edge groups.* Dies at two points:
   - `C ∩ aCa^{-1}` can be infinite of infinite index, so 2-transitivity does not bound `[A:C]`;
   - there is no normal subgroup of `C` to kill that leaves finite factors.
   `osin-group-times-z-has-bvc` (not finitely presented) shows this must fail without finite
   presentation: `O × Z` is an HNN extension over the non-VC `O` and has BVC.
3. *Elementary amenable groups of infinite Hirsch length* (`bvc-elementary-amenable-groups-have-finite-hirsch-length`).
   Looked at briefly; no progress, nothing written.
4. *Ascending HNN extensions of free groups.* The idea was residual finiteness (Borisov–Sapir,
   recalled) plus known classes. Not pursued: it rests on recollections that could not be
   verified after the search budget ran out.
5. *Alternative for the HNN case.* `N` is a directed union of VC groups, so `G` is elementary
   amenable of Hirsch length 2, and `elementary-amenable-finite-hirsch-length-bvc-groups-are-vc`
   would apply. Not used, to keep the route on the vPW import rather than a newer node.

## What remains open

- The hole `fp-bvc-groups-without-vc-splittings-are-finite`: infinite finitely presented BVC groups
  with no splitting over a VC subgroup. Two sub-cases stay fully open:
  - torsion-free groups with finitely many conjugacy classes;
  - ascending HNN extensions over non-VC finitely generated bases.
- Checking the overlap claims above against sources (Minasyan–Osin; vPW 1704.05304 Theorem I).

## Literature consulted (literature gate, 2026-09-16)

- von Puttkamer–Wu, arXiv:1607.03790v2 (via the repo artifact
  `research/artifacts/zp-jpl-bvc-known-classes-2026-09-13.md`, which read Lemmas 1.7, 1.11, 2.4,
  Proposition 1.12, Corollary 1.15).
- von Puttkamer–Wu, arXiv:1704.05304 (Theorem I, as recorded in that artifact).
- Semantic Scholar list of papers citing 1607.03790: 2210.15746 (published Math. Ann. 392 (2025)
  1747–1779), 2007.02988, 1807.10095, 1704.05304, 1712.00496, 1710.04935, and 2602.17411 (Feb
  2026, no BVC content found). None resolves Conjecture A or B.
- Web searches for "von Puttkamer Wu conjecture BVC finitely presented" and variants: no
  resolution found. 2603.13096 and 2511.21293 came up and are irrelevant. The search budget ran
  out mid-session, so the Minasyan–Osin overlap was not rechecked.
- Lyndon–Schupp, *Combinatorial Group Theory*, Ch. IV §2 (normal form and conjugacy theorem
  IV.2.8), used as the landed amalgam route uses it, not re-read.

## Referee (2026-09-16)

**Checked.**

- All six files, in full. `git status` shows no unlisted files from this lane.
- The landed inputs, read in full: `bvc-amalgams-have-two-transitive-vertex-actions` with its
  `-proof`, `non-ascending-hnn-extensions-lack-bvc`, `virtually-solvable-bvc-groups-are-virtually-cyclic`,
  `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension` and the target.
- Artifact §0–§4, line by line:
  - (V1)–(V6), including the transfer argument in (V4) and the reflection centralizers in (V5);
  - Lemma 0; the class bound Lemma 1 under property P;
  - the rigidity Lemma 2, with the normal-form bookkeeping `c = a c_1 a^{-1}`;
  - Proposition 3; the counting Lemma 4, where rotations of different reduced forms are absorbed
    by conjugation by `C`, so at most `m|Q|` per class;
  - the index formula `[A:C] = 1 + [C:D_a]`; normality of `<z^{R_A R_B}>` and the pushout
    quotient;
  - the virtual-solvability arguments. In the HNN case these are `F_k = F(H)` for all `k` via
    (V5) and equal orders, the abelian normal `M` of index at most 2 in `N/L`, and
    `G/N ≅ Z`.
- No hidden finite-generation assumption: (V3) uses only that VC groups are finitely generated.
  The (CT) statement (cyclic permutation, then conjugation by `C`) matches the form used by the
  landed route and by von Puttkamer–Wu's own proof of Lemma 1.10.
- Citation numbers checked against the arXiv LaTeX source of 1607.03790v2 (fetched
  2026-09-16):
  - Lemma 1.10 (free products), Lemma 1.11 (KMN 5.6), Proposition 1.12 (virtually solvable),
    Lemma 2.4 (non-ascending HNN);
  - Proposition 3.2 (acylindrically hyperbolic groups lack BVC), Corollary 3.3(a) (hyperbolic),
    Corollary 3.4 (surjection onto an AH group).
  Minasyan–Osin Corollary 2.2 was checked against the source of 1310.6289. arXiv:2210.15746 is
  Barnea–Camina–Ershov–Lewis on NCC(G) and is not about BVC. The Semantic Scholar citer list
  and 2602.17411 were not rechecked, because the web-search budget was exhausted.

**Changed.**

1. Lemma 0 now states its last step, that `C_Γ(L)` is solvable.
2. The claim and artifact Corollary 1 no longer say that the splitting theorem shows a non-VC
   BVC group is not virtually free. For groups that are not finitely generated that does not
   follow from the theorem. The fact is now attributed to von Puttkamer–Wu Lemmas 1.10 and 1.11,
   which do give it.
3. Novelty corrected in the claim, the artifact §5 and above. The theorem follows, with no finite
   generation, from Minasyan–Osin Corollary 2.2 plus von Puttkamer–Wu 3.2, 3.4, 1.12 and 2.4. The
   lane's contribution is a self-contained elementary proof.

**Verdict.**

- The mathematics is sound. The proof route is a complete argument from landed claims and the
  standard normal-form and conjugacy theorems.
- The reduction route is valid but, as the solver says, it only relocates the difficulty. The
  new hole is equivalent to the target given the theorem, and it carries an honest '## Attempts'
  section.
- Landed with fixes.

