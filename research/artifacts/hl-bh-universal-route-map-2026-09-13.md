# Boone–Higman: status of the universal routes, 2026-09-13

Lane `hl-bh-universal`. Target: `boone-higman-conjecture`.

**Source.** `cairn why boone-higman-conjecture` on a fresh MSI clone at main
`7e6f60b57`, run with `/usr/bin/python3.12 tools/cairn.py`. The compile printed
foreign errors, but `why` completed:
- `a2-kernel-removal-iff-image-satisfies-pbh` is an unknown claim;
- three Bowen–Chapman artifact paths are missing.

## 1. Census

- **Routes into the root:** 24.
- **Dead or excluded:** 10.
- **Live:** 14.
- **A live route that is not universal:** `pbh-via-bh-and-a2-kernel-removal`, and
  `permutational-boone-higman-via-mif-envelopes` inside the PBH route, both
  require `boone-higman-conjecture` itself. So they can't prove it.

## 2. Dead routes and what killed them

| Route | Invalidated by |
|---|---|
| `boone-higman-via-bffhz-action-image` | `bffhz-action-image-is-finitely-presented` refuted |
| `boone-higman-via-ck-quotient-cosets` | `ck-quotient-coset-repair` refuted |
| `boone-higman-via-finitely-presented-simple-ring-quotient` | `rank-four-elementary-center-obstructs-simplicity`; `finite-fullness-simulation-theorem-for-rings` refuted |
| `boone-higman-via-hypothesis-free-shift-compiler` | `compilers-cannot-drop-the-decidability-hypothesis` |
| `boone-higman-via-maximal-quotient-of-the-envelope` | `fp-quotient-iff-kernel-finitely-normally-generated` |
| `boone-higman-via-rover-nekrashevych-hosts` | `deligne-lattice-embeds-in-no-rover-nekrashevych-group` |
| `boone-higman-via-sandwich-ring-simplicity` | `one-sided-sandwich-leaves-an-ideal-missing-the-core` |
| `boone-higman-via-shift-higman-compiler` | `shift-higman-compiler` refuted (trivial input) |
| `boone-higman-via-universal-fp-self-similar-host` | `self-similar-hosts-contain-only-residually-finite-groups` |
| `boone-higman-via-universal-leavitt-host` | `fixed-leavitt-hosts-cannot-be-universal-bh-containers`, `weyl-algebra-blocks-a-universal-leavitt-host` |

## 3. Live routes, grouped by host shape, with their open premises

**(a) Cantor shell and full Cantor groups.** Five routes. The complexity wall does
not apply, because every shell envelope contains its input.
- `boone-higman-via-fp-shell-envelopes` needs `decidable-inputs-have-fp-shell-envelopes`.
- `boone-higman-via-perfect-shell-envelopes` needs `perfect-decidable-inputs-have-fp-shell-envelopes`.
- `boone-higman-via-shell-germ-stabilizers` needs `decidable-inputs-have-fp-shell-stabilizers`.
- `boone-higman-via-enlarged-shell-stabilizers` and `boone-higman-via-shell-stabilizer-overgroups`
  need `perfect-shell-pairs-have-finite-biindex-fp-hosts`.

Recorded obstructions, all necessary-condition results and none a kill:
- free-product near actions;
- one-ended shift normalization (B = λ(P) never works);
- Belk–Hyde–Matucci Corollary 2.10 fails outside virtually cyclic inputs;
- rational regular actions;
- fixed-base odometer charts for inputs with an infinite Kazhdan subgroup.

No finite presentation of any one-singularity stabilizer is known for an input
that is not virtually cyclic.

**(b) Permutational hosts.** Four routes.
- `boone-higman-via-permutational-boone-higman`: its universal premise is
  `decidable-groups-embed-in-orbit-finite-affine-actors`, via covered Cantor-module
  actors.
- `boone-higman-via-infinite-shift-compiler` needs `infinite-shift-higman-compiler`
  (Mallery–Zaremsky envelopes).
- `boone-higman-via-fiber-product-criterion` needs
  `universal-fiber-product-data-for-word-problem-groups`. Its specialization
  `every-wp-group-embeds-in-fp-conjugacy-finite-group` is **refuted here** (Section 4).
- `boone-higman-via-finite-bi-index-envelope` needs
  `ck-envelope-simple-core-has-finite-bi-index`. This is the shape of Zaremsky's
  Corollary 5.11, with the Chatterji–Kassabov envelope.

**(c) Algebraic ring hosts.** Four routes.
- `boone-higman-from-infinite-simple-inputs` via
  `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`.
- `boone-higman-via-central-simple-leavitt-tensor-host` via
  `decidable-group-algebras-have-fp-central-simple-hosts`.
- `boone-higman-via-projective-ring-host` via
  `decidable-group-ring-has-fp-projective-simple-host`.
- `boone-higman-via-ck-maximal-kernel` via
  `ck-envelope-has-a-finitely-normally-generated-maximal-kernel`.

The shared wall: finite generation of a maximal ideal or normal subgroup, or
equivalently a finitely presented simple algebra over the input. Fixed host
families die by the complexity wall.

**(d) Structural closure.** One route.
- `boone-higman-via-decidable-edge-towers` needs both
  `decidable-groups-embed-in-decidable-edge-towers` and
  `bh-embeddability-survives-decidable-edge-hnn`.
- By `fa-subgroups-of-graph-towers-lie-in-base-pieces`, FA inputs must already lie
  in the base.

## 4. New this lane: the conjugacy-finite premise is false

`thompson-v-embeds-in-no-conjugacy-finite-group` (ESTABLISHED, elementary):
- conjugation preserves element orders, so a group with `k` conjugacy classes has
  at most `k` orders;
- the left-comb prefix code `1, 01, ..., 0^(n-2)1, 0^(n-1)` gives an order-`n`
  element of `V` for every `n`;
- `V` is finitely presented and simple, hence decidable.

So `V` lies in no conjugacy-finite group, and the universal premise fails at
`G = V`. The general fiber-product data survives: only the conjugacy-finite
normal subgroup `N` is forced to have finitely many element orders.

## 5. The test input every universal route must pass

Deligne's lattice `Gamma~` is finitely presented, decidable, Kazhdan, with infinite
center, and not residually finite. It is excluded from:
- Rover–Nekrashevych hosts;
- self-similar hosts;
- amenable-orbit full groups;
- eventually similar hosts with RF vertex groups;
- fixed-base shell charts;
- being its own type (A) actor.

Any universal proof must reach `Gamma~`, or an overgroup of it, through one of
the fourteen live routes. Route (d) must put `Gamma~` in its base.

## 6. Exact gap

Every live universal premise is open, and none is implied by established
material. The cheapest still-plausible attacks are a finite presentation of the
one-singularity shell stabilizer `A_1` for a one-ended input such as `Z^2` (route
(a)), and the covered Cantor-module universality question (route (b)).
