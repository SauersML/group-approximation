# gq graph-health status, pass 1 (2026-09-17, lane gq-integrate)

Scope: every node landed by the GL_n(Q) swarm through `gqland.sh`. At the end of this pass that was 103
landings and 235 node files, read from `origin/main` (tip `2ede07731` at the last read). The shared
checkout is behind `origin/main`, so nothing was read from it and nothing was written to it.

## 1. What was checked, and how

- **Hand lint of every gq node, read with `git show origin/main:<path>`:**
  - id equals the file stem and matches `^[a-z0-9][a-z0-9-]{1,63}$`;
  - `rg: 2`, `kind: claim|route` and `title` are present;
  - frontmatter keys are within Cairn's allowed set;
  - every artifact path exists on `origin/main`;
  - every route target is an existing claim, and every `requires` id is an existing claim;
  - claims carry `distinct_from`.
- **One `cairn check`, run on a private extract:**
  - The extract was `origin/main` at `05c0707b2` (`research/` and `tools/`), written to lane scratch, never to
    the checkout.
  - Its only errors on gq nodes were `missing title` on routes.
  - Every other error was an artifact path outside `research/`, absent from the extract by construction.
  - The warnings are pre-existing dependency cycles, none through a gq node, plus the generic "open tops off
    a root path" count.
- **Status consistency.** The graph statuses were recomputed from routes, with `invalidates` applied (the
  alternating fixpoint, which is total here: no undefined claims). The result was compared with each gq
  claim's stated bold status.
  - Before this pass, two claims stated ESTABLISHED had no route, so the graph computed them as OPEN:
    `germ-extensions-omit-standard-gl-n-q` and `proper-semisimple-cat0-groups-contain-no-gl-2-q`.
  - After this pass every gq claim's stated status matches the computed one.
  - The root `gl-n-q-embeds-in-fp-simple-group` computes OPEN.

## 2. Fixes landed

| Commit | Change |
|---|---|
| `75cf1f5ae` | Titles for 14 routes that had none (the only `cairn check` errors on gq nodes) |
| `37f7ed114` | Titles for 20 more untitled routes that landed during the pass |
| `c1ec40220` | Direct-proof routes `germ-extensions-omit-standard-gl-n-q-proof` and `proper-semisimple-cat0-groups-contain-no-gl-2-q-proof`, pointing at the proofs already written in the targets; no mathematics added |
| `27deb1b9c` | Root: obstruction pointers O5 (`gl-n-q-hosts-cannot-act-on-one-manifolds`) and O6 (the scaled-rational-line invariant) |
| `2603283c9` | Root: Attempts item 15, an index of the established obstructions that the root did not cite |

The root has a single `## Attempts` section, items 1–15, and obstructions O1–O6.

**Cause of the title errors.** The route template in RULES §4 lists `kind`, `target` and `requires` but not
`title`, and `gqland.sh` does not lint for it. Every untitled route followed that template. Until the template
and the lander are fixed, new untitled routes will keep arriving.

## 3. Routes into the root: all wired, each one hole short

| Route | Open prerequisite |
|---|---|
| `gl-n-q-bh-via-leavitt-resolvent-units` | `leavitt-resolvent-derived-units-mod-centre-fp-simple` |
| `gl-n-q-via-harmonic-cuntz-host` | `harmonic-cuntz-simple-group-is-finitely-presented` |
| `gl-n-q-via-projective-elementary-hosts` | `q-algebra-with-fp-simple-projective-elementary-group` |
| `gl-n-q-bh-via-rational-leavitt-simple-group` | `rational-leavitt-simple-group-embeds-in-fp-simple-group` |
| `gl-n-q-bh-via-binary-leavitt-unit-group` | `gl-n-q-embeds-in-binary-leavitt-unit-group` |
| `gl-n-q-bh-via-permutational-class` | `gl-n-q-in-permutational-boone-higman-class` |
| `gl-n-q-root-via-nontrivial-psl-maps` | `psl-n-q-maps-nontrivially-to-fp-simple-groups` |
| `gl-n-q-root-via-just-infinite-hosts` | `sl-odd-q-has-fp-just-infinite-host` |
| `gl-n-q-via-gl-infinity-q` | `gl-infinity-q-embeds-in-fp-simple-group` |
| `gl-n-q-root-from-countable-decidable-bh` | `countable-decidable-groups-embed-in-fp-simple-groups` (equivalent to Boone--Higman) |

Established inputs that these routes lean on, and that were landed as "lane proof, not independently
reviewed":
- `leavitt-resolvent-ring-is-fp-simple-of-char-zero` and `fp-simple-ring-of-characteristic-zero-exists`,
  which assert a finitely presented simple ring of characteristic zero containing `Q`, with referee requests
  sent;
- `harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q`;
- `q-algebra-elementary-quotients-contain-gl-n-q`.

No referee artifact for any of them was on `origin/main` at this pass. The only referee artifacts were
`gq-referee-a-pp-circle-divisible-subgroups-act-freely.md` and
`gq-referee-b-sl-n-q-is-colimit-of-lattice-stabilizers.md`.

## 4. Open gq claims on no path to a root

Consequences of the root, reached through routes that *require* the root, so they are not its prerequisites:
- `gl2-q-embeds-in-fp-simple-group`, `sl2-q-embeds-in-fp-simple-group`, `psl2-q-embeds-in-fp-simple-group`;
- `u3-q-embeds-in-fp-simple-group`;
- `gl-n-qbar-embeds-in-fp-simple-group`, `number-field-gl-n-embeds-in-fp-simple-group`;
- `countable-char-zero-linear-groups-embed-in-fp-simple-groups`.

Side questions:
- `gl-n-f2t-embeds-in-fp-simple-group`, with `rational-function-field-embeds-in-binary-leavitt-algebra`;
- `leavitt-units-over-s-integers-are-finitely-presented`;
- `sl-n-q-is-colimit-of-lattice-stabilizers`.

These are the "open tops on no live path to a root" that `cairn check` warns about. No wiring was added for
them: a route into the root is a mathematical claim, not lint. If the n = 2 and U_3(Q) stepping stones are
program targets in their own right, they would need `root: true`; that is left to team-lead.
