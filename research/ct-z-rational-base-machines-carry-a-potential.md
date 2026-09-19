---
rg: 2
id: ct-z-rational-base-machines-carry-a-potential
kind: claim
title: "Rational-base Turing machines in CT_{3}(Z): junk reflection by direction switching works, but an exact realization exists iff the machine's states carry a rational potential, and a potential makes every net tape change a function of (initial state, current state, head displacement), so such machines cannot store unbounded information and this coding cannot transport Kari–Ollinger's theorem"
---

**ESTABLISHED** (lane proof, not reviewed). Elementary. No priority is claimed.
- This carries out the next step named in `ct-z-monomial-elements-have-decidable-torsion`: a
  junk-reflection gadget for rational-base Turing machines.
- **Finding.** The gadget exists (Theorem 2), but the route it serves is closed by a conservation
  law (Theorems 1 and 3).
- **Open.** The torsion problem of `CT(Z)` stays **OPEN**.

## Setting: the coding class

`T` is a complete reversible Turing machine in the moving-tape model of Belk–Bleak / Kari–Ollinger.
It has alphabet `{0, 1}`, and its instructions are moves `(s, L/R, s′)` and writes `(s, k, s′, l)`.
Work in `CT_{3}(Z)` with active coordinates `Z_2 × Z_3` and slopes `2^i3^j`. Put `r = 2/3`.
- **Left tape.** `x_2 = P_s + r^ℓ·Lcode(τ_L)`, with `Lcode(a·τ) = α_a + r·Lcode(τ)`. The digits
  `α_0, α_1 ∈ Z_(2)` have distinct parities. The prefix balls `P_s + 2^ℓZ_2` are distinct for
  distinct states.
- **Right tape.** `x_3 = Θ_s + β_{a_0} + r^{-1}·Rcode(τ′)`, with `Rcode(a·τ) = β_a + r^{-1}Rcode(τ)`.
  - The values `β_0, β_1, β_J` form a complete residue system mod 3, and `J` is the unused
    residue, the **junk**.
  - The top digit carries a state-dependent offset `Θ_s`.
- **Exactness.** Each instruction is one piece `x ↦ qx + c` for each state and read symbol, with
  `q = r` (right move), `r^{-1}` (left move) or `1` (write).
- Theorem 2 of `ct-z-torsion-problem-and-the-brin-thompson-transplant` shows why this is the
  natural class. Transfers are the only way to move digits between the two tapes, and slope-1
  pieces are integer translations acting on both.

## Statement

**Theorem 1 (the potential criterion).**
- **Claim.** `T` has an exact realization in this class iff there are `K ∈ Q` and a map
  `Ψ : states → Q` (the *potential*) with:
  - `Ψ_{s′} = rΨ_s − K` for each right move `(s, R, s′)`;
  - `Ψ_{s′} = r^{-1}(Ψ_s + K)` for each left move;
  - `Ψ_{s′} = Ψ_s + (β_l − β_k)` for each write `(s, k, s′, l)`.
- **What the potential is.** `Ψ_s = P_s − Θ_s`.
- **Normalizing.** Given a potential, all residue and integrality conditions can be met. Replacing
  `Ψ` by `Ψ + const` and rescaling, one may take `K = 0` and `β_1 − β_0 = 1`.

**Theorem 2 (junk reflection).**
- **Construction.** Let `T` have a potential. Add a direction bit (`Ψ` equal on both copies) and use
  Kari–Ollinger direction switching at junk:
  - go forward by `T`, and reverse direction when the next step would read or pop `J`;
  - go backward by `T^{-1}`, and reverse when its next step would read or pop `J`.
- **Result.** This gives a class-wise order-preserving `g_T ∈ RCWA(Z)` with `{2,3}`-smooth moduli (in
  `CT_{3}(Z)` when its pieces are canonical; see the caveat below), and `g_T` has finite order iff
  `T` is uniformly periodic.

**Theorem 3 (a potential freezes the tape).**
- **Setting.** Take `K = 0`, `β_1 − β_0 = 1`, and a run of `T` from `(s_0, τ_0)`. Let `s_t` be the
  state at time `t`, `D_t` the head displacement, and `Δ_p ∈ {−1, 0, 1}` the net change of cell `p`
  by time `t`.
- **Conservation law.** `Σ_p Δ_p r^{D_t − p} = Ψ_{s_t} − r^{D_t} Ψ_{s_0}`.
- **Consequence.** The net tape change is determined by `(s_0, s_t, D_t)`. In particular, whenever
  the run returns to its initial state and head position, the tape is exactly restored.
- **So** potential machines have no storage beyond state and head position. They cannot carry the
  unbounded counters that Kari–Ollinger's undecidability proofs store on the tape. No exact
  realization in this class makes the torsion problem undecidable through Kari–Ollinger.

## Proofs

**Theorem 1.** In each case, compare the constant `c` forced by `Z_3` with the one forced by `Z_2`.
- **Right move `(s, R, s′)`, top symbol `a`.** Here `q = r`.
  - On `Z_3`, `x_3 = Θ_s + β_a + r^{-1}(β_b + r^{-1}ρ)` must go to `Θ_{s′} + β_b + r^{-1}ρ`. This
    forces `c = Θ_{s′} − r(Θ_s + β_a)`, independent of `b`.
  - On `Z_2`, `P_s + r^ℓz` must go to `P_{s′} + r^ℓ(α_a + rz)`. This forces
    `c = P_{s′} + r^ℓα_a − rP_s`.
  - Equating: `Ψ_{s′} − rΨ_s = −rβ_a − r^ℓα_a`. This must not depend on `a`, which forces
    `α_a = −r^{1−ℓ}β_a + κ`, and then `Ψ_{s′} = rΨ_s − K` with `K = r^ℓκ`.
- **Left move.** Here `q = r^{-1}`. The same comparison gives
  `Ψ_{s′} − r^{-1}Ψ_s = β_a + r^{ℓ−1}α_a = r^{-1}K`, with the same linkage of `α` and `β`.
- **Write.** Here `q = 1`. On `Z_2`, `c = P_{s′} − P_s`. On `Z_3`,
  `c = Θ_{s′} + β_l − Θ_s − β_k`. Equating gives the write rule.
- **Sufficiency.**
  - **Normalize.** Shift `Ψ` by the fixed point `−3K` of `Ψ ↦ rΨ − K`, so `K = 0`.
  - **Digits.** Take `β_0 = 0`, `β_1 = 2^{ℓ−1}`, `β_J ≡` the third residue mod 3, all in `Z[1/2]`.
    Then `α_0 = 0` and `α_1 = −3^{ℓ−1}`, which is odd.
  - **Offsets.** `Z[1/2]` is dense in `Q_2`, so choose `Θ_s ∈ Z[1/2]` with
    `P_s = Ψ_s + Θ_s ∈ Z_(2)` in any prescribed class mod `2^ℓ`.
  - **Integrality.** Each piece is integral at 2 by its `Z_2` formula, at 3 by its `Z_3` formula,
    and at every `p ≥ 5` because its constant lies in `Z[1/6]`. So it maps its class onto a class.
- **Bijectivity.** `Φ` is a homeomorphism from (valid states) × `{0,1}^N` × `{0,1,J}^N` onto the
  valid-state balls, and invalid-state balls are fixed. So the pieces tile, and the element is a
  bijection of `Z` with positive slopes.
- **A caveat.** Membership in `CT(Z)`, not just in class-wise order-preserving `RCWA(Z)`, also needs
  every piece to be canonical (`r ↦ s` on least residues). The potential does not guarantee this. ∎

**Theorem 2.**
- **The switched system is realized.** Let `Halt_J` be the forward configurations whose `T`-step
  would read or pop `J`, and `Init_J` the backward ones whose `T^{-1}`-step would. Kari–Ollinger's
  switching `D` is a bijection, exactly as the switching machine `D` of
  `ct-z-conjugacy-problem-is-undecidable`. A switch is a slope-1 piece changing only the direction
  bit, with `c = P_{s,bwd} − P_{s,fwd} = Θ_{s,bwd} − Θ_{s,fwd}`; this is where `Ψ` equal on both
  copies is used. So Theorem 1 realizes `D`.
- **If `T^N = 1`.** For a configuration `x`, let `x̃` replace every `J` by `0`.
  - The `T_J`-run from `x` agrees with the `T`-run from `x̃` until it needs a `J` cell. So within
    `N` steps it either closes up or reaches `Halt_J`, and likewise backward within `N` steps.
  - So every `D`-orbit has length at most `4N + 2`, and `D^{(4N+2)!} = 1` on the active coordinates.
  - On each piece of that power, the rational affine map fixes an open set of `Z_2 × Z_3`. So it is
    the identity on all coordinates.
- **Conversely.** On `J`-free forward configurations `D = T`, so finite order forces uniform
  periodicity. ∎

**Theorem 3.**
- **The identity.** Put `W_t = Ψ_{s_t} − r^{D_t}Ψ_{s_0}`.
  - A write at displacement `p` adds `l − k` to `W`.
  - A right move multiplies `W` by `r`, and a left move by `r^{-1}`.
  - So `W_t = Σ_i (l_i − k_i) r^{D_t − p_i}`. Writes to the same cell telescope to its net change
    `Δ_p`, since each write reads the current value.
- **Uniqueness.** `Σ_p Δ_p r^{e_p} = 0`, with distinct `e_p` and `Δ_p ∈ {−1, 0, 1}`, forces all
  `Δ_p = 0`.
  - Multiply by `3^M 2^{−m}`, where `M` and `m` are the largest and smallest exponents.
  - The term with `e_p = M` is `Δ_p 2^{M−m}`, which is prime to 3 unless `Δ_p = 0`. Every other term
    is divisible by 3.
- **Conclusion.** So `(Δ_p)` is determined by `W_t`, hence by `(s_0, s_t, D_t)`. For `s_t = s_0` and
  `D_t = 0`, `W_t = 0` and the tape is restored. ∎

## What this says

- **Where the obstruction sits.** Junk is not the obstruction. Exactness is.
  - Every write is an additive change, and a single shared constant `c` spreads it to every active
    coordinate. The only place it can go is the finite control, as the potential.
  - A finite control holds finitely many potentials, and the base-`3/2` uniqueness law (Theorem 3)
    then forbids storing anything.
- **Relation to V.** This is the arithmetic form of the reason `V` has solvable torsion problem: a
  one-stack machine cannot compute. In `CT_{3}(Z)` two stacks exist, but the shared slope couples
  them through a conserved rational quantity.
- **Consequences for 21.74(a).**
  - (G1) is not reachable by any exact rational-base coding, nor by counter-machine step maps
    (`ct-z-monomial-elements-have-decidable-torsion`).
  - Lane bh-free-57 shows that any `2V` in `CT_P(Z)` needs germ-degree rank at least 2 (a138a1757).
- **Leaning (not claimed).** The torsion problem of `CT(Z)` is decidable. If so, `2V` does not embed
  in `CT(Z)`, by Theorem 1 of `ct-z-torsion-problem-and-the-brin-thompson-transplant`. A proof
  would need a structure theorem for `ĝ` on `Ẑ_S` in the spirit of revealing pairs.

## Lesson for general BH

**A shared slope creates a conservation law, and conservation laws kill storage.**
- When one affine map acts on every coordinate, every write is recorded in a single rational
  quantity. Exact codings force that quantity to live in the finite control.
- A digit-uniqueness law (base `3/2` with digits `−1, 0, 1`) then makes all net tape changes a
  function of the control and the head position.
- **For BH hosts.** To run unbounded computation uniformly, as a compiler or wrapper must, the host
  needs *independent* coordinate actions, with no conserved quantity linking them (`nV`,
  twisted `SV_G`).
- **In the other direction.** Conserved quantities are a source of decidability. They are the
  likely engine of a positive solution to the torsion problem of `CT(Z)`, and perhaps of 21.74(a).
