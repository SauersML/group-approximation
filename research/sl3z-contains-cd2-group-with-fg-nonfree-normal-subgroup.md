---
rg: 2
id: sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup
kind: claim
title: SL_3(Z) contains a finitely generated subgroup of cohomological dimension two with a finitely generated, non-free normal subgroup of infinite index
distinct_from:
  sl3z-contains-cd2-euler-positive-fibered-subgroup: that asks for a fibration onto Z with nonzero Euler characteristic and type FP; this drops the Euler characteristic and allows any infinite quotient, asking only for a non-free finitely generated normal subgroup of infinite index (the fibred case implies this one)
  sl3z-contains-rfrs-cd2-subgroup-with-positive-b2: that asks for a virtually RFRS cd-two subgroup with positive second L2-Betti number and no normal-subgroup structure; this asks for a normal-subgroup structure with no residual or L2 hypothesis
  sl3z-infinite-index-normal-fibers-force-zariski-density: that is a necessary condition, Zariski density of such a configuration; this is the existence statement
  sl3z-is-incoherent: that is the bare existence of a finitely generated non-finitely-presented subgroup; this is a structured witness from which non-finite-presentability follows by Bieri's theorem, and the converse is not known
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

There are a finitely generated subgroup `G <= SL_3(Z)` with `cd G <= 2` and a
normal subgroup `N ◁ G` that is finitely generated, of infinite index in `G`,
and not free.

By `sl3z-incoherent-via-bieri-normal-subgroup`, `N` is then not finitely
presented, so `SL_3(Z)` is incoherent. The fibred Euler-characteristic target
`sl3z-contains-cd2-euler-positive-fibered-subgroup` implies this claim
(`sl3z-euler-fibered-subgroup-gives-bieri-witness`).

**Necessary conditions on a witness `(G, N)`** (artifact, Section 7).

- `G` is torsion-free and `cd G = 2`. If `cd G <= 1`, then `G` and `N` are
  free.
- `N` is not finitely presented. So `N` is Zariski dense and of infinite
  index in `SL_3(Z)` (`sl3z-incoherence-witnesses-are-zariski-dense-thin`).
- `N` is not virtually solvable. Finitely generated solvable subgroups of
  `GL_3(Z)` are polycyclic, hence finitely presented.
- `C_G(N) = 1`, so the monodromy `G/N -> Out(N)` is injective. `C_G(N)`
  centralizes a Zariski-dense subgroup, so it is central in `SL_3` and trivial
  in `SL_3(Z)`.
- Every stabilizer in `G/N` of the `N`-conjugacy class of an infinite-order
  element of `N` is polycyclic
  (`sl3z-normal-subgroup-class-stabilizers-are-polycyclic`).
- `G` has no normal subgroup isomorphic to `F_2`.
  - Otherwise, by `sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients`,
    `G` would be virtually `F_2` or virtually `F_2 x| Z`.
  - Such a group is coherent: free-by-cyclic groups are coherent
    (Feighn–Handel, recalled, not re-read), and coherence passes to
    finite-index overgroups.
  - Then `N` would be finitely presented.

## Attempts

- 2026-09-16 (hi-fron-zaremsky-3-04-sl3z-coherent): introduced as the
  Bieri-type reformulation of the fibred criterion.
  - Proved that criterion C1 implies this claim. A free fibre would make the
    group a mapping torus of a rose, which has Euler characteristic zero.
  - Recorded the necessary conditions above.
  - No witness was found, and no obstruction was found.
  - Lemma S constrains `(G, N)` only when `G/N` is large and some
    infinite-order class has a finite orbit.
  - Proposition A does not apply, because `N` is not free.
- Long–Reid strategy, *Small subgroups of SL(3,Z)*, 2010 preprint,
  Proposition 5.2, read 2026-09-16. It seeks `N = ρ_k(F) ∩ Δ_k` inside a
  torsion-free finite-index `Δ_k <= ρ_k(Γ)`, where `Γ` is the figure-eight knot
  group and `F` is its fibre.
  - Their Theorem 4.1 gives `ρ_k(F)` of finite index in `SL(3,Z)` for
    `k = 0, 2, 3, 4, 5`, so those values fail.
  - A faithful `ρ_k` fails because `N ≅ F_2`.
  - Open: some `k` with `ρ_k(Γ)` thin of virtual cohomological dimension 2
    and `ρ_k(F)` not virtually free.
