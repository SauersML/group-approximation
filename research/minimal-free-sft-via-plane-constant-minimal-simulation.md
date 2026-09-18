---
rg: 2
id: minimal-free-sft-via-plane-constant-minimal-simulation
kind: route
title: Clapham envelope, an effective minimal free subshift on it, and a Durand--Romashchenko minimal simulation one Z^2 factor up
target: decidable-groups-embed-in-fp-groups-with-minimal-free-sft
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-fp-groups-have-effective-minimal-free-subshifts
  - effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts
---

**Route. OPEN.** The implication below is complete. The route fires once the
two OPEN premises (M2) and (M1) are proved.

**Decomposition.**
- **(M2)** `decidable-fp-groups-have-effective-minimal-free-subshifts`:
  existence of an effective minimal free subshift over the envelope. It is pure
  existence and can fail without any SFT.
- **(M1)** `effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts`:
  a group version of Durand--Romashchenko. It is pure simulation and can fail
  even when (M2) holds.

The two premises fail independently.
- (M1) is proved for no infinite nonabelian `Λ_0` and has its own obstruction:
  exponential reading pressure.
- (M2) is proved for no simple Kazhdan envelope and dies for Zorn-style
  constructions.

**Necessity inside the design class.** By
`plane-constant-minimal-sft-factors-are-effective-minimal`, any proof of (P1)
through a minimal SFT over `Λ_0 x Z^2` whose `Λ_0`-freeness comes from a free
plane-invariant factor already contains (M2) for `Λ_0`. So (M2) is forced by
the design and is not an artifact of this route.

**How this differs from the recorded attempts on (P1).**
- Attempt 1 passes to a minimal subsystem of a strongly aperiodic SFT and loses
  finite type.
- Attempt 2 pulls back a minimal `Z^2`-SFT and loses freeness.
- Here freeness is imported from the free factor `Y` (M2), and minimality with
  finite type from the simulation (M1).

## Proof of the implication

Let `K` be finitely generated with solvable word problem.

1. **Envelope.** By `clapham-fp-embedding-preserves-word-problem`, `K` embeds
   in a finitely presented `Λ_1` with solvable word problem. Put
   `Λ_0 = Λ_1 x Z`.
   - `Λ_0` is finitely presented, as a direct product of finitely presented
     groups.
   - It is infinite.
   - It has solvable word problem: normal forms split into coordinates.
   - It contains `K`.
2. **(M2).** There is a nonempty, effectively closed, minimal, free subshift
   `Y ⊆ B^{Λ_0}`.
3. **(M1).** Applied to `Λ_0` and `Y`, it gives a nonempty minimal SFT
   `X ⊆ A^Λ` with `Λ = Λ_0 x Z^2`, and a continuous `Φ : X -> Y` with:
   - `Φ((λ,0)·x) = λ·Φ(x)`;
   - `Φ((1,z)·x) = Φ(x)`;
   - `Z^2` acting freely on `X`.
4. **`Λ` is admissible.** `Λ = Λ_1 x Z x Z^2` is infinite and finitely
   presented, and contains `K`.
5. **`X` is free.** Suppose `(λ,z)·x = x`. Since `(λ,z) = (1,z)(λ,0)`,

   ```text
   Φ(x) = Φ((λ,z)·x) = Φ((1,z)·((λ,0)·x)) = Φ((λ,0)·x) = λ·Φ(x).
   ```

   `Φ(x) ∈ Y` and `Λ_0` acts freely on `Y`, so `λ = 1`. Then `(1,z)·x = x`, and
   `Z^2`-freeness gives `z = 0`.
6. **Conclusion.** `X` is a nonempty SFT over `Λ` on which `Λ` acts minimally
   (M1) and freely (step 5). This is (P1) for `K`.

**Effect on Boone--Higman.** (P1) is premise 1 of
`boone-higman-via-v-times-aperiodic-sft-full-groups`. After this route, that
route's open leaves are (M1), (M2) and (P2)
`v-times-minimal-free-sft-alternating-full-groups-are-fp`.
- (M2) is needed only for the Clapham envelopes `Λ_1 x Z` of infinite simple
  Kazhdan inputs (`boone-higman-iff-simple-kazhdan-decidable-inputs`).
- (M1) is needed only for the effective minimal free subshifts that (M2)
  produces.
