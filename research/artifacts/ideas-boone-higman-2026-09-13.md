# Ideation: Boone–Higman, hard-WP fp simple groups, PBH — 2026-09-13

Lane `ideas-boone-higman`. Task: generate genuinely novel routes, quick-kill,
name the best still-open one and its exact obstruction. No node is marked
ESTABLISHED here; this is an idea log. Facts attributed to the literature below
are cited from memory and were **not pinned at source in this lane** — flagged
inline.

## The one filter every idea must pass

`complexity-bounded-host-classes-are-not-universal` (ESTABLISHED on main): if a
class of hosts shares one recursive word-problem time bound, some two-generated
decidable group embeds in no member. So a universal Boone–Higman construction
**must consume the input's word-problem algorithm** and make the host at least
as hard. Equivalently `fp-simple-groups-with-arbitrarily-complex-word-problem`
is a necessary consequence. Every "fixed nice host family" idea dies here; only
*input-adaptive* constructions survive. `clapham-fp-embedding-preserves-word-problem`
lets every idea assume the input is finitely presented for free.

## 12 ideas, with kill/alive verdict

1. **Input-encoded Cuntz–Krieger full group.** Build a one-sided SFT / CK
   groupoid `G_E` from the input's multiplication table (not from a fixed
   alphabet); take Matui's simple, type-F_∞ commutator full group `D([[G_E]])`.
   Input-adaptive, so it can pass the wall. *Distinct from* the dead
   `boone-higman-via-shift-higman-compiler` (trivial input) and the twisted
   `SV_G` route (which twists a fixed shift by a G-action = PBH). **ALIVE,
   PROMISING.** Obstruction below.
2. **Existentially closed within the decidable class.** e.c. groups are simple
   (Macintyre, *cited*), every countable group embeds in one; ask for an fp
   group e.c. *relative to fp decidable groups*. Beautiful reframing. **ALIVE as
   a reformulation**, but e.c.-in-all has undecidable WP (embeds undecidable
   inputs), and "fp + e.c.-in-class" is not obviously weaker than BH — I could
   not verify an equivalence, so no claim landed. Mark: reformulation, unproven.
3. **Turing machine as reversible cellular automaton → alternating full group.**
   Encode the WP algorithm as a reversible CA; take Nekrashevych's simple
   alternating full group of its germ groupoid. Input-adaptive. Converges onto
   idea 1 once "CA" is read as "groupoid". **ALIVE, = idea 1.**
4. **Contracting self-similar host.** *DEAD*: `self-similar-hosts-contain-only-
   residually-finite-groups` — Deligne's lattice (non-RF) is excluded.
5. **Outer extension of one fp simple group.** *DEAD as an advantage*:
   `outer-extension-word-problem-is-kernel-bounded` — no complexity gain over BH.
6. **Simple Steinberg/Leavitt algebra unit group over the input.** Live route (c)
   on main but crowded (255 Steinberg nodes); wall = "fp simple algebra over the
   input". **ALIVE but already staffed.**
7. **Non-RF Burger–Mozes lattice in a product of two trees, VH-structure encoding
   the algorithm.** BM simple lattices are fp, simple, non-RF. But CAT(0) ⇒ no
   Baumslag–Solitar, no exponentially distorted subgroups, and biautomatic ⇒
   polynomial WP. A *fixed* BM class is wall-excluded; an input-dependent VH
   complex must encode the algorithm into the local action. **ALIVE, hard**;
   `product-of-trees-faithful-factor-pbh-via-bass-serre-induction` is the nearest
   existing node.
8. **Boundary full group of an input-built hyperbolic group.** Overlaps shell
   envelopes (Belk–Hyde–Matucci), heavily on main. **ALIVE but likely dup.**
9. **Priority / finite-injury construction of a simple fp group meeting simplicity
   requirements.** 55 kleene + 32 priority nodes already on main. **ALIVE, dup
   risk high.**
10. **AF / Bratteli–Vershik groupoid.** *DEAD*: AF ⇒ amenable/RF-flavored, cannot
    hold non-amenable decidable inputs.
11. **Minimal Z-subshift full group.** *DEAD*: Juschenko–Monod (*cited*) — these
    are amenable, so no non-amenable input embeds.
12. **Decidable-edge HNN tower (route d).** The surviving *structural* shape:
    `bh-embeddability-survives-decidable-edge-hnn` and
    `decidable-groups-embed-in-decidable-edge-towers`, both OPEN. Input-adaptive
    by construction (edges carry the algorithm). **ALIVE, the most classical.**

## Three best (one line each)

- **(1) Input-encoded Cuntz–Krieger / SFT full group** — make the *groupoid*,
  not a twist, carry the input; harvest Matui simplicity + finite presentation.
- **(12) Decidable-edge HNN tower** — force simplicity by HNN steps whose edges
  are finitely generated with decidable membership; the one missing permanence.
- **(7) Input-dependent non-RF product-of-trees lattice** — the only host family
  that is simultaneously fp, simple, non-RF, and geometric.

## Deep look at idea 1, and its exact obstruction

Setup. For a fp decidable `G`, want a CK/Katsura groupoid `G_E` with:
- `G_E` minimal and purely infinite ⇒ `D([[G_E]])` simple and of type F_∞
  (Matui, *cited, not pinned*), hence finitely presented, and non-amenable;
- a faithful embedding `G ↪ D([[G_E]])`;
- `G_E` built from `G`'s presentation/algorithm so the host WP scales with `G`'s
  (needed for the complexity wall, since a *fixed* CK full group is a
  Higman–Thompson `V`-type group with polynomial WP).

**The obstruction (why it is not free).** Matui's fp full groups `D([[G_E]])`
for a *fixed finite* graph `E` are exactly Higman–Thompson–Matui groups — their
word problems are uniformly low (`V`-like), so by the complexity wall no fixed
family is universal. To scale complexity one must vary `E` with `G`, but then the
embedding `G ↪ D([[G_E]])` is exactly the unproven content: the only known
general embedding mechanism into CK/Röver–Nekrashevych simple groups is
self-similarity, which is `self-similar-hosts-contain-only-residually-finite-
groups`-dead for non-RF inputs. So idea 1 collapses onto the same wall as the
twisted route unless a **non-self-similar embedding of `G` into a purely infinite
minimal groupoid's full group** is produced. That is the precise open premise,
and it is not on main under any of the shift-compiler, `SV_G`, or self-similar
headings.

**Cheapest decisive test.** Take `G = Z^2` (one-ended, not virtually cyclic, the
same test input where `square-spiral-z2-near-shift-group-is-not-finitely-
presented` stopped route (a)). Does `Z^2` embed in `D([[G_E]])` for some purely
infinite minimal `G_E`, with the embedding not landing in a rational/self-similar
copy of `V`? If even `Z^2` resists, the route is as hard as the shell route; if it
succeeds, push to Deligne's lattice `Gamma~`, the universal test input.

## Note for the coordinator

`cairn check` on main currently fails for every lane on two *foreign* breakages,
not from this lane: the claim `a2-kernel-removal-iff-image-satisfies-pbh` is
referenced by three `a2-kernel-removal-*` nodes but absent, and several
`GroupApproximation/BowenChapman/*.lean` artifact paths are missing. Both should
be routed to their owners.
