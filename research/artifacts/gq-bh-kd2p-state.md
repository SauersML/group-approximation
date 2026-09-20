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
| Every counter cycle must contract, so partial contraction is impossible on the top (`K = 2` and all `K`) | `kms-top-every-counter-cycle-must-contract` (3860416431) | **referee PASS** (bh-ref-g, 28f69471d1), three minor repairs applied |
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

## Referee update (bh-ref-g, 28f69471d1)

- **Every-cycle contraction: PASS.** The repairs are applied: `Z_0 = P^1(F_{p^r}) \ {0, 1, ∞}`, minimal
  polynomials for Galois orbits, and the unit ratio over `F_p`.
- **Lamp mixing: PASS, but narrower.**
  - `t = 1` holds only for domains containing a counter pair `(u, 1 − u)`. For power-type domains `U^n` the
    augmentation factors through the lamp ring, so **central lamp mixing is not excluded** there.
  - Step 2's injectivity is unjustified, since `F_p[Q]` has zero divisors.
  - The `H^1` reduction passes.
- **So there are two live routes.**
  - (i) Counter cocycles: a nontrivial `H^1` class.
  - (ii) Central lamp mixing `F(A_0) = tA_0` with `t ∈ T_0`, on a power-type domain `U_H ⊆ ker(ev_z)`, where
    every counter in the domain equals 1 at a point `z` whose coordinates `s_i` and `1 − s_i` are roots of unity.

## Update (lane bh-kd2p-2, same day): route (i) collapses into route (ii)

`kms-counter-cocycles-reduce-to-central-lamp-mixing` (lane proof, not reviewed).
- **Module facts.** `B_0` fixes `T_0`. On `T/T_0` every counter satisfies `ã_i − 1 = ã_i'` (G5a, G5b, G6, G2),
  so `T/T_0` is a module over `F_p[v_i^{±1}, (v_i − 1)^{-1}]`.
- **Vanishing.** If some image counter `g` has `g − 1` invertible there (for instance `ã_j^{±p^f}`, as in the
  Kochloukova–Sidki shape), then `H^*(U_H, T/T_0) = 0` and `H^1(U_H, T) ≅ Hom(U_H, T_0)`.
- **Consequence.** A counter-mixed lift is conjugate by `s ∈ T` to a central counter twist (invisible on the
  torsion part) plus the central lamp mixing `F(A_0) = τ·f̄(A_0)`, `τ = s(f̄(A_0) − 1) ∈ T_0`.
- **So only route (ii) is live, and for counter-pair domains it dies too.** What is left: route (ii) on
  power-type domains (does `N = {b ∈ 𝔟 : ε(f̄^n b) = 0 ∀n}` still contain a nonzero invariant ideal?), and top
  maps whose image counters share a common unit point `z` (e.g. all of `ã'`-type).

## Update 2 (lane bh-kd2p-2): route (ii) closed at the lamp level

`kms-central-lamp-mixing-cannot-separate-top-core` (lane proof, not reviewed).
- **Result.** In the product Frobenius–Möbius class, with a non-contracting cycle, the refereed invariant
  principal ideal of `kms-top-every-counter-cycle-must-contract` can be built, with a larger field `F_{p^r}` and
  exponent `N'`, inside `𝔪_z`, where `z` is the point the mixing character factors through. On that ideal the
  lift equals `f̄`, so central lamp mixing never separates the top core, power-type domains included.
- **Both lamp-level routes are now closed** (route (i) under hypothesis (V)).

**Exact remaining cases for KD2_p:**
1. `F` on `H ∩ T`: the normal closure `I·[T, I]` of the top core must fail to be `F`-invariant inside `H`. This
   is the only place separation can still happen, and it is the same check for every lift.
2. Route (i) without (V): every image counter shares a common unit point `z`.
3. Mixing into grades other than `T_0`, or into `B_1, …, B_K`.
4. Top maps outside the product Frobenius–Möbius class.
5. `p = 2`.

## Update 3 (lane bh-kd2p-2, after bh-ref-g's review 941f051f16): the precise live route

- **Corrections.** `kms-counter-cocycles-reduce-to-central-lamp-mixing` passes its computations. But "both
  routes die" is withdrawn: the top core is not normal in `G(M)`. Since `A_0` acts nontrivially on `T` (G5a), any
  normal subgroup containing a nonzero lamp ideal `I` also contains `[T, I] ⊆ T_0`. The corollary now covers
  every domain lamp, and the Kochloukova–Sidki shape reads `ψ(ã_K) = ã_1`.
- **What is closed.** The lamp and counter components of a lift cannot separate the top core. Counter cocycles
  reduce to central lamp mixing, under (V). Central lamp mixing vanishes on a refereed-type core ideal inside
  `𝔪_z`, on every domain (unreviewed).
- **THE LIVE ROUTE: mixing through `F` on `T ∩ H`.** A hard self-similar KMS lift must separate the top core by
  its configuration part. Take the invariant ideal `I` (built inside `𝔪_z` if needed). The lift is faithful only
  if no normal subgroup `N` with `I ⊆ N ≤ I·T` lies in `H` and is `F`-invariant. That comes down to how `F` acts on
  `[T, I] ⊆ T_0`. The first test: `K = 2`, trivial machine, top map of Kochloukova–Sidki shape made
  non-contracting on one cycle, and `F|_{T∩H}` any `ψ`-semilinear map compatible with G5a–G6. Does some choice
  push `[T, I]` out of every `F`-invariant subgroup inside `H`?
