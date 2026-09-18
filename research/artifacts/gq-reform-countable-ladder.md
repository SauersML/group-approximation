# Boone–Higman reformulations for the countable input GL_n(Q): what survives

Lane `gq-reform-countable`, 2026-09-17. Landed nodes: 63495ddd7, a6c28b163 and
45e18ac43. The type (A) / Alt_fin / twisted Brin–Thompson forms belong to lane
`gq-typeA-design` (7ee358237) and are not repeated here.

## 1. The key move: simple inputs

For odd `m`, `SL_m(Q)` is simple, infinite, and contains `GL_n(Q)` for `n < m`
(`sl-odd-q-simple-inputs-for-gl-n-q-root`). Every per-input principle of the repo
that needs a simple input therefore applies to the root. A nontrivial
homomorphism of `SL_m(Q)` is already an embedding.

## 2. Repo reformulation → per-input form for GL_n(Q)

| Repo node (class-level, f.g. inputs) | Countable per-input form | Status |
|---|---|---|
| `boone-higman-iff-infinite-simple-inputs` | inputs `SL_m(Q)`, `m` odd, are simple (§1) | ESTABLISHED |
| `boone-higman-iff-fp-just-infinite-hosts` | `simple-group-in-fp-simple-iff-fp-just-infinite-host` (any infinite simple `S`, no f.g., host just-infinite above a *nontrivial image*) → target `sl-odd-q-has-fp-just-infinite-host` ⟺ root | tool ESTABLISHED, target OPEN |
| `local-boone-higman-iff-boone-higman` (c) | `sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially`: one existential sentence about any one fp overgroup; ladder BH ⇒ BH(H_m) ⇒ BH(P_m) ⇒ Σ_(P_m,s) ⇒ root | ESTABLISHED |
| `local-boone-higman-iff-boone-higman` (a)⟺(b) | *fails per input*: local holds (`gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups`), global is the open root | local ESTABLISHED |
| `boone-higman-iff-isolated-hosts-and-local-boone-higman`, per-input form | needs an isolated overgroup `H` and the universal theory of fps groups *on H*. For simple inputs the discriminating set is one element, so isolation is not needed (the criterion node) | subsumed |
| `boone-higman-iff-simple-kazhdan-decidable-inputs` | `GL_n(Q) ⊂ P_m ⊂ H_m`, with `H_m` f.g. simple Kazhdan and decidable, so the root reduces to BH for the single group `H_m` (criterion node, clause 4) | ESTABLISHED |
| survey Cor 3.5 | `countable-decidable-groups-embed-in-fp-simple-groups` ⟺ BH, routed into the root and into `countable-char-zero-linear-groups-embed-in-fp-simple-groups` | OPEN (= BH) |

## 3. What does not transfer, and why

- **Class-level ⟺ does not give per-input ⟺.** The converse directions of the
  repo's equivalences apply BH to an *envelope* of the input (the Thompson
  envelope, the Clapham envelope). For one countable input this is only a
  sufficient condition. Per input, the only two-sided statements are the
  just-infinite criterion and the one-sentence criterion. Both need simple inputs.
- **Local-to-global fails for non-f.g. inputs.** Every finitely generated
  subgroup of `GL_n(Q)` embeds (Zaremsky), so every universal sentence of fps
  groups holds in `GL_n(Q)`. The root is pure uniformity, and no argument by
  finite pieces reaches it.
- **Host calibration** (in `sl-odd-q-has-fp-just-infinite-host`):
  - residually finite hosts are excluded, and so are lattices in linear
    algebraic groups;
  - cocompact CAT(0) hosts, including all Burger–Mozes lattices, are excluded,
    because their abelian subgroups are finitely generated while `Q` is not.

## 4. Weakest sufficient statements specific to GL_n(Q) (all ⟺ root unless noted)

1. For infinitely many odd `m`: a nontrivial homomorphism `SL_m(Q) -> Γ` with `Γ`
   finitely presented and just-infinite above the image.
2. For some odd `m >= n + 1` and some finitely presented `P ⊇ SL_m(Q)`: a
   homomorphism of `P` to a finitely presented simple group that does not kill
   one fixed `s`. For a *fixed* `P` (a Problem 2.7 overgroup, the survey's
   decidable `P_m`) this is sufficient, not equivalent.
3. `GL_n(Q) ∈ B_A` (lane gq-typeA-design).
