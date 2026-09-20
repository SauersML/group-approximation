# KD2_p, lane bh-kd2p: consolidated state, 2026-09-19

Crux: `two-counter-kms-groups-are-self-similar` (KD2_p), **OPEN**. The target is a hard two-counter KMS group
`G(M)`, in characteristic `p`, inside a finitely generated self-similar group.
- By bh-birget (2222dfd660, unreviewed), the Zaremsky endgame needs only a relator kernel that is a finitely
  generated lift ideal, not finite presentation.
- No priority is claimed. The machinery is Kochloukova–Sidki (arXiv:1710.04745), Kochloukova–Luiz
  (arXiv:2509.05798), Dantas–Sidki (arXiv:1505.05165) and Kharlampovich–Myasnikov–Sapir (arXiv:1204.6506v5).

## Results

| result | node (landing) | status |
|---|---|---|
| For `p` odd, `B_K` embeds with index 2 in a finitely presented, transitive self-similar metabelian group (Kochloukova–Sidki Theorem D with `g = 1 + x`, via `s ↦ −x`); the Kochloukova–Luiz kill does not transfer to characteristic `p` | `kms-tops-embed-in-fp-self-similar-metabelian-groups` (e09c2a9b3f, bb1c51d165) | **referee PASS** (bh-ref-q11, d143aa5b5e; it repairs K–S's Lemma 7.1 proof) |
| The full top `Q = B_1 × ⋯ × B_K × B_0` embeds in a finitely presented self-similar group for `p` odd; Lemma 1: some counter must move the root (`K ≥ 2`); G6 gives a necessary condition; Part 3 sketch: contracting lifts are too easy | `kms-configuration-lift-needs-non-contracting-counters` (7ee3e78b5c, b24f87cfd1) | Part 0 and Lemma 1 **PASS**; Part 2 remark; Part 3 sketch (bh-ref-q11, b5cae104ff) |
| Hartogs extension of the lamp map (`K ≥ 2`); uniform non-contracting renormalizations of Frobenius–Möbius type are unfaithful; no unipotent part (sketch) | `kms-top-renormalizations-must-contract` (b24f87cfd1) | unreviewed (queued with bh-ref-q11) |
| Theorem M: mixed exponents, with no contracting cycle, are unfaithful; the dummy-counter shortcut fails; design constraint `F(A_0) = tA_0` with `t ∈ T_0` | `kms-lift-must-mix-top-core-into-configurations` (c20f9bed2c) | unreviewed (queued) |
| Every counter cycle must contract, so partial contraction is impossible on the top (`K = 2` and all `K`) | `kms-top-every-counter-cycle-must-contract` (this landing) | unreviewed |
| Referee repairs of bh-ref-c (6c39124b28) | applied in ed3dbbb573's node, the crux node, and the gate-1 artifact (e09c2a9b3f) | done |

## Where KD2_p lives now

- **On the top, faithfulness forces contraction on every counter cycle.** This is proved in the product
  Frobenius–Möbius class, which tropical rigidity suggests is all of them (sketch).
- **Contraction makes configuration equality polynomial.** This is a sketch and conditional.
- **So a hard lift must not preserve `B_0`.** Its image modulo `T` has a nonzero core on `B_0`, which the
  `T`-components must separate.
- **The concrete next step.** Find `t ∈ T_0 = ⟨x_{qA_0}⟩` with `F(A_0) = tA_0`, compatible with G4 under the
  induced map on `B_0` and with G6 on the `x_{q_j}`, whose iterates separate `B_0`'s core.
  - `t(A_0 − 1)^{p−1} = 0` holds automatically, by G5c.
  - The machine's counters `a_i` sit in one-variable factors, where isometric (division) renormalizations are
    allowed.
- **`p = 2`.** Open. An `F_4` version of Theorem D (Frobenius `x^4`) is a spark and has not been checked.

## Split with other lanes

- bh-birget owns Birget's question by non-KMS routes, and the increment-only test case (c) (99e3f37a25).
- bh-kd2p owns the KMS top and the lamp-into-`T` construction.

## LESSONS lines (in board/LESSONS.md)

- Frobenius twists make characteristic-`p` Krull-dimension-`d` metabelian groups self-similar.
- Hardness and contraction are incompatible on the counters (sketch).
- On the KMS top, non-contracting renormalizations are unfaithful (Hartogs).
- Faithfulness on the top costs contraction on every cycle, and the leftover core must be absorbed by `T_0`.

## Update (same day): the smallest explicit mixing fails

`kms-lamp-mixing-dies-on-br-relation`: `F(A_0) = tA_0` with `t ∈ T_0` is incompatible with G4.
- **Why.** G4 is inhomogeneous in `A_0`, and `B_0` centralizes `T_0`. This is proved for domains containing a
  counter pair `(u, 1 − u)`, as Kochloukova–Sidki's does.
- **Surviving route.** The mixing goes through the counters: `F(ã_i) = t_i α_i`, a 1-cocycle whose lamp
  components `t_g(A_0 − 1)` land in `T_0`. Only a nontrivial class in `H^1` helps, since coboundaries are inner.
- **Next step.** Compute `H^1(F̄(H ∩ B_0), T)` on the counters, for the smallest instance: `K = 2` and the
  trivial machine.
