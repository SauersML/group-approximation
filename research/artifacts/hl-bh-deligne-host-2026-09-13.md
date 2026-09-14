# Deligne's lattice as the Boone–Higman test input, 2026-09-13

Lane `hl-bh-deligne-host`. Target: `deligne-lattice-satisfies-boone-higman`,
which stays **OPEN**.

Here `Gamma~` is the preimage of `Sp_4(Z)` in the universal cover of `Sp_4(R)`.
It is finitely presented, decidable, Kazhdan, has infinite center, and is not
residually finite. By `research/artifacts/hl-bh-universal-route-map-2026-09-13.md`,
every universal route into `boone-higman-conjecture` must reach it.

## 1. Host families at `P = Gamma~`

| Family | Status at `Gamma~` | What decides it |
|---|---|---|
| Residually finite, linear, self-similar hosts | dead | `Gamma~` is not residually finite |
| Rover–Nekrashevych `V_d(H)` | dead | `deligne-lattice-embeds-in-no-rover-nekrashevych-group` |
| Amenable-orbit full groups | dead | `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` |
| Fixed-base shell charts | dead | `fixed-base-shell-inputs-embed-in-odometer-rn-groups` |
| `Gamma~` as its own type (A) actor | dead | `type-a-actors-have-no-infinite-virtually-central-subgroup` |
| Haagerup hosts (`V`, `T`, `F`) | dead | property (T) against a proper affine action |
| **Eventually similar hosts, any groupoid** | **circular (new)** | `deligne-lattice-eventually-similar-hosts-are-circular` |
| Shell envelopes `E_nu`, singularity stabilizers | open | finite presentation of `A_1`, `A_12`, `A_2`; `R_nu` must be an ascending HNN extension over a finitely generated base |
| Mallery–Zaremsky envelopes `E_nu(P)` | open | `infinite-shift-higman-compiler` at `P = Gamma~` |
| Covered Cantor-module actors | open | `decidable-groups-embed-in-covered-cantor-module-actors` at `P = Gamma~` |
| Fiber-product data | open | the conjugacy-finite specialization is refuted (878979e3c); general data untested |
| Chatterji–Kassabov simple core | open | finite bi-index of the simple core |
| Ring hosts | open | a finitely presented simple algebra over the input |
| Decidable-edge towers | open | `Gamma~` has property FA, so it must lie in a base piece |
| Brin–Thompson `nV` | untested | cone markings are not commensurated (`brin-thompson-brick-charts-are-not-commensurated`) |

## 2. New theorem: eventually similar hosts are circular

`fw-nst-inputs-virtually-embed-in-one-vertex-group`, proved in
`fw-nst-one-vertex-group-proof`:
- **Input.** An FW group `K` with a central infinite cyclic `Z`, such that every
  normal subgroup of every finite-index subgroup has finite index or is
  virtually in `Z`.
- **Conclusion.** Inside any eventually similar host, `K` lands, up to finite
  index and a finite normal subgroup, in ONE vertex group, with `Z` intact.
- **Proof.** The coordinate kernels of the product embedding can't all contain a
  power of `z`.

`deligne-lattice-eventually-similar-hosts-are-circular`, proved in
`deligne-eventually-similar-circularity-proof`:
- **(D) for `Gamma~`.** Margulis's theorem, imported verbatim through
  `higher-rank-lattice-normal-subgroups-central-or-finite-index`, sends normal
  subgroups to central or finite-index ones. Deligne's non-residual finiteness
  rules out a normal subgroup of finite-index image meeting the center
  trivially, since it would split off `Z` and make `Gamma~` residually finite.
- **What the vertex group must contain.** Some vertex group contains `L / F`,
  which is:
  - not residually finite, because `z^2` lies in the finite residual and survives;
  - of infinite center;
  - without any type (A) action.

So eventually similar hosts, including graph almost-automorphism groups and every
eventually self-similar groupoid over a shift of finite type, give no reduction for
`Gamma~`. They can only move the question inside a vertex group.

## 3. Directive items not achieved

- **(a) A type (A) overgroup built from the central extension.** Arithmetic
  subgroups with finitely many double cosets aren't available over `Z`:
  parabolic double cosets are infinite already for `B(Z) <= SL_2(Z)`. Actions on
  Maslov lifts of rational Lagrangians keep `z` central, and the Maslov difference
  is an unbounded pair invariant. No candidate was found.
- **(b) Ring hosts over symplectic Steinberg groups.** If a ring `R` has
  `KSp_2(R)` torsion or zero, any map `Gamma~ -> StSp(R)` induced from `Z -> R`
  kills a power of `z`. Leavitt algebras over fields are an example, because
  their K-theory vanishes (Ara–Brustenga–Cortiñas; not re-read). This is a heuristic
  remark only and was not landed.
- **(c) A family kill.** Section 2 is circularity, not a kill. Any kill of a
  universal family at `Gamma~` must involve finite presentation. Every host family
  still open for `Gamma~` contains `Gamma~` by construction whenever it
  contains any input.

## 4. Exact gap

- **Positive.** A finitely presented host containing `Gamma~` in which `z` has
  infinitely many conjugates, through:
  - finite presentation of a shell stabilizer at `P = Gamma~`;
  - a Mallery–Zaremsky envelope;
  - a covered Cantor-module actor; or
  - a Brin–Thompson group `nV`.

  An embedding into `nV` would also show that `nV` is not a-T-menable. That
  would answer Zaremsky Problem 2.7 negatively, since `2V`'s Haagerup and Kazhdan
  properties are open (web search, 2026-09-13).
- **Negative.** A finite-presentation obstruction that uses property FW or
  Deligne's residual `<z^2>` inside one of those host shapes. None is known.
