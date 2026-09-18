# gq graph-health status, pass 2 (2026-09-18, lane gq-integrate)

Scope: every node landed by the GL_n(Q) swarm through `gqland.sh`. By this pass that was 324 landings and 456
node files, read from `origin/main` (tip `b82951dcd`). Pass 1 is `ceecf6bb6`. Nothing was read from or written
to the shared checkout.

## 1. Text fixes landed in this pass (`3befe79c8`)

- `bs13-embeds-in-brin-thompson-3v`:
  - "What it would give" is now "What it gives", in indicative wording, citing the priority check
    (gq-lit-arxiv, `e78b09c00`).
  - The novelty statement now names the untwisted groups `nV`. Bux–Llosa Isenrich–Wu (arXiv:2408.05673)
    already place every Baumslag–Solitar group in a twisted `SV_G`.
- `smart-induced-on-genuine-moves-has-exact-tripling`:
  - The "Not established" renormalization paragraph now points to the ESTABLISHED
    `smart-induced-map-has-brick-local-height-3-renormalization` (referees a, b, c PASS).
  - The two stale `distinct_from` lines were updated.
- `fp-simple-ring-of-characteristic-zero-exists`: cites the three PASS reports on
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero`. It also notes that the equivalence of the stated forms
  was not refereed separately.
- The four proof routes named in `gq-gq-fp-simple-rings-char-zero-writeup.md` §7 now cite their PASS reports:
  - `fp-simple-q-algebras-embed-in-fp-simple-rings-proof`: referee b, and referee a for parts 1–3 only;
  - `char-zero-representable-rings-embed-in-fp-simple-rings-proof`;
  - `fg-semiprime-pi-q-algebras-embed-in-fp-simple-rings-proof`;
  - `resolvent-vacuum-rings-have-no-k0-state-proof`.

Every cited report was checked on `origin/main` and reads PASS.

## 2. Lint (hand, over all 456 gq files)

The checks are the pass-1 checks: id, `rg`, `kind`, `title`, target and requires resolve to claims, and
artifacts exist.
- No errors. No untitled routes remain.
- One claim lacks `distinct_from`: `steinberg-finite-presentation-and-kazhdan-theorem`. It also has no bold
  status line. It computes ESTABLISHED through `steinberg-finiteness-kazhdan-citation`. gq-referee-c passed
  n ≥ 5 with a self-contained proof, and n = 4 as a literature import (Krstić–McCool).

## 3. Status consistency

Statuses were recomputed from a private extract at `b82951dcd`, with routes and `invalidates`, by the
alternating fixpoint. The result is total. Of the 233 gq claims, 176 compute ESTABLISHED.

- **Root G**, `gl-n-q-embeds-in-fp-simple-group`: computes OPEN.
- **Root G′**, `gl-n-q-explicit-natural-fp-overgroup` (Problem 2.7): computes ESTABLISHED, through
  `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring` and `gl-n-q-all-n-in-st-10-of-resolvent-ring`. This
  matches its text, which leaves naturality to experts.
- The three claims stated REFUTED each have an established `refuted_by`:
  - `capacity-chain-resolvent-ring-has-rational-k0`;
  - `leavitt-resolvent-derived-units-mod-centre-fp-simple`;
  - `sl3-toeplitz-harmonic-elementary-groups-are-fp`.

**Mismatches not fixed.** This pass was text-only, and each fix changes the graph.

1. **Circular wiring.** `capacity-chain-presentation-is-not-simple-proof` requires
   `capacity-chain-resolvent-ring-has-rational-k0`, the candidate that the target refutes.
   - The route uses it only for notation (the presentation). Its proof builds a module that satisfies every
     relation.
   - So the graph establishes neither the refutation nor `register-comparison-presentations-are-not-simple`,
     which requires it. The candidate does not compute REFUTED.
   - Proposed fix: `requires: []` in that route, keeping the notation reference in the body.
2. **`one-steinberg-group-contains-every-gl-n-q`** is stated ESTABLISHED "through the proof in Attempts 1",
   with no route.
   - Referees a and c pass it conditional on four classical `K_2` citations. Referee b's report is on main.
   - The two `St_4` routes into G′ therefore cannot fire: `gl-n-q-explicit-via-st-4-of-resolvent-ring` and
     `gl-n-q-explicit-via-st-4-of-divisible-ring`.
   - It needs a proof route whose `requires` lists its inputs (owner gq-deep-free-1).
3. **`sl2-casimir-cannot-separate-verma-from-finite-dimensional`** is stated ESTABLISHED ("standard `sl_2`
   representation theory") with no route (owner gq-k2-q).

## 4. Routes into root G

There are ten routes, each with exactly one prerequisite that does not compute ESTABLISHED.

| Route | Missing prerequisite |
|---|---|
| `gl-n-q-bh-via-leavitt-resolvent-units` | `leavitt-resolvent-derived-units-mod-centre-fp-simple`, **REFUTED** by `leavitt-resolvent-derived-units-mod-centre-not-fp`, so the route is dead |
| `gl-n-q-via-harmonic-cuntz-host` | `harmonic-cuntz-simple-group-is-finitely-presented` |
| `gl-n-q-via-projective-elementary-hosts` | `q-algebra-with-fp-simple-projective-elementary-group` |
| `gl-n-q-bh-via-rational-leavitt-simple-group` | `rational-leavitt-simple-group-embeds-in-fp-simple-group` |
| `gl-n-q-bh-via-binary-leavitt-unit-group` | `gl-n-q-embeds-in-binary-leavitt-unit-group` |
| `gl-n-q-bh-via-permutational-class` | `gl-n-q-in-permutational-boone-higman-class` |
| `gl-n-q-root-via-nontrivial-psl-maps` | `psl-n-q-maps-nontrivially-to-fp-simple-groups` |
| `gl-n-q-root-via-just-infinite-hosts` | `sl-odd-q-has-fp-just-infinite-host` |
| `gl-n-q-via-gl-infinity-q` | `gl-infinity-q-embeds-in-fp-simple-group` |
| `gl-n-q-root-from-countable-decidable-bh` | `countable-decidable-groups-embed-in-fp-simple-groups` (equivalent to Boone–Higman) |

Neither the dead route nor the root's Attempts yet records the refutation that kills
`gl-n-q-bh-via-leavitt-resolvent-units`.
