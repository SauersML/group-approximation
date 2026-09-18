---
rg: 2
id: baumslag-gersten-port-route-fails-at-the-dilation-centralizer
kind: claim
title: The port route to Baumslag-Gersten (HNN of BS(1,2) along cofinite abelian ports, kernel removed by generation) fails at its first step; power-conjugate cyclic edge groups are never cofinite ports, and in the odometer-baker host the dilation has cyclic centralizer by Curtis-Hedlund-Lyndon, so no cofinite port contains it
requires:
  - prime-odometer-groups-generate-class-wise-increasing-rcwa-p
  - higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness
  - odometer-2v-is-fp-simple-and-contains-bs12
distinct_from:
  prime-odometer-groups-generate-class-wise-increasing-rcwa-p: that removes a gluing kernel by generation when the ports are odometers; this shows that for Baumslag-Gersten the port on the dilation side cannot exist in the canonical host, so generation is never reached.
  higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness: that names faithfulness as the missing clause of Higman closure; this finds an earlier failure for BS-type HNN extensions, namely the existence of the port itself.
---

**ESTABLISHED** for items 1–3 (lane bh-invent-02, 2026-09-18). These are lane proofs,
elementary. They have not been reviewed, and no priority is claimed. Item 4 is the verdict.

## The route tested

`BG = ⟨a, t | b^-1 a b = a^2, b = t^-1 a t⟩` is the HNN extension of `BS(1,2) = ⟨a, b⟩` along
`t^-1 a t = b`. The port route has three steps.

- **(S1) Ports.** Find a host `D ⊇ BS(1,2)` on a set `X` with cofinite free abelian
  subgroups `A_0 ∋ a` and `A_1 ∋ b`, and an isomorphism `φ: A_0 → A_1` of port actions with
  `φ(a) = b`.
  - Then `BG ≤ D *_φ` by Britton's lemma, once `BS(1,2) ∩ A_0 = ⟨a⟩` and
    `BS(1,2) ∩ A_1 = ⟨b⟩`.
  - `D *_φ` is a relative host (`higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness`,
    item 2).
- **(S2) Faithfulness.** `BG` meets the free kernel of `D *_φ ↷ X` trivially.
- **(S3) Generation.** The image of `D *_φ` is a Li-finite full group, as in
  `prime-odometer-groups-generate-class-wise-increasing-rcwa-p`.

## Statement

1. **Power-conjugate elements are never cyclic ports.** Suppose `x` is conjugate to `x^k`
   (`|k| ≥ 2`) in a group acting on an infinite set, and `⟨x⟩` has finitely many orbits.
   This is impossible. In BG the edge elements `a`, `b` and all `t^-i a t^i` are
   power-conjugate. So every port of this splitting has rank at least 2.
2. **The `a`-side port exists.** Let `D = F((F_2^+ × F_2^+) ⋈ Z^2)`, with the two odometers
   `τ_1 = τ × id` and `τ_2 = id × τ` acting on the two colours.
   - `D` is `F_∞` by Li's Example ex:ZS (III): the action is pseudo-free, and
     `D^*(w,w) = Z^2`.
   - `D` acts faithfully on the orbit `X = Z × Z` of the eventually constant pairs. It
     contains Brin's `2V` and `BS(1,2) = ⟨a, β⟩` with `a = τ_1`, where `β(x, y) = (σx, x_0 y)`
     is the baker map (`odometer-2v-is-fp-simple-and-contains-bs12`).
   - `A_0 = ⟨τ_1, τ_2⟩ ≅ Z^2` acts regularly on `X` and contains `a`.
3. **The `b`-side port does not exist.** Let `D′` be any group of homeomorphisms of `C × C` whose
   germs at every point are prefix replacements composed with odometer powers on the two
   tails. This covers `2V`, `2V_τ` and `D`. Then `C_{D′}(β) = ⟨β⟩`. So `β` lies in no
   abelian subgroup of rank at least 2, and `⟨β⟩` has infinitely many orbits on `X`. No
   cofinite port contains the dilation.
4. **Verdict.**
   - In the canonical host the route **fails at (S1), on the dilation side**. Steps (S2)
     and (S3) are never reached.
   - The precise open gate is a host containing `BS(1,2)` in which the dilation `b`
     commutes with a cofinite `Z^n` (`n ≥ 2`).
   - By item 3, that host cannot be a finite-modification-of-tails group in which `b` acts
     as a shift.

## Proof

**Item 1.** Let `x` have `c` infinite orbits. Then `x^k` has `|k|·c` infinite orbits. Conjugate
permutations have equal cycle counts, so `c ∈ {0, ∞}`. Finitely many `⟨x⟩`-orbits would then
make them all finite, so `X` would be finite. In BG, `b^-1 a b = a^2`, and conjugating by powers
of `t` transports this to every `t^-i a t^i`, including `b`.

**Item 2.**
- `τ_1` and `τ_2` commute. `(i, j) ↦ (i+1, j)` and `(i, j+1)` are the translations of
  `Z × Z`, so the action is regular.
- The relation: with `x ↔ i` read least significant digit first,
  `β(i, y) = (⌊i/2⌋, 2y + (i mod 2))`. So `β a^2 = a β`, i.e. `β^-1 a β = a^2`.

**Item 3.**
- **`β` is the shift.** Identify `C × C` with `{0,1}^Z` by `z_i = x_i` (`i ≥ 0`),
  `z_{-1-j} = y_j`. Then `β` is the shift `σ`.
- **Commuting elements are cellular automata.** Let `g ∈ D′` commute with `σ`. By
  Curtis–Hedlund–Lyndon, `g` is a cellular automaton with some local rule `f` of radius `R`.
- **The rule is a projection.** Take `z` with every word occurring infinitely often in its
  right tail. Near `z`, `g` replaces a prefix `u` by `u′` and applies `τ^j` to the tail.
  `τ^j` changes only finitely many digits of such a tail.
  - So `g(z)_i = z_{i - d}` for all large `i`, with `d = |u′| - |u|`.
  - Every word of length `2R+1` occurs in that region, so `f` is the projection to one
    coordinate, the same one for every piece.
- **Conclusion.** Hence `g = σ^{-d}`, and `C_{D′}(β) = ⟨β⟩`.
- **Orbits.** `σ` has infinitely many orbits on the eventually constant bi-infinite
  sequences, one for each finite pattern up to shift. ∎

## Lesson for general BH

**Ports must be parabolic.** Power-conjugacy forces every edge group of a Baumslag–Solitar-type
HNN extension to sit in a port of rank at least 2. The conjugating element must then sit in the
port on the other side.

In Thompson and odometer hosts that conjugating element is hyperbolic, a shift. Shifts have
cyclic centralizers there, by Curtis–Hedlund–Lyndon rigidity: a map that commutes with the
shift and changes tails only finitely is a power of the shift.

**What this means for the route.**
- Higman's operations along cofinite ports can glue only along parabolic (odometer-like)
  subgroups.
- The BS chains behind BG and the one-relator targets of BBMZ 5.3(9) need gluing along
  hyperbolic data. So they need a host in which the BS dilation is non-expansive.
- This is the permutational form of the recorded lessons that power-conjugacy works against
  finiteness (bh-free-09) and that compiler drift blocks stacking (bh-invent-08).
