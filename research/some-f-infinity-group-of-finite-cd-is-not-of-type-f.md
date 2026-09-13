---
rg: 2
id: some-f-infinity-group-of-finite-cd-is-not-of-type-f
kind: claim
title: "Some group of type F_infinity with finite cohomological dimension is not of type F"
---

There is a group `G` of type `F_∞` with `cd G < ∞` and no finite `K(G,1)`. By
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd`, such a `G` has `G × Z` of type F,
so it answers Problem 1.21 negatively (`zaremsky-1-21-by-no`).

**What any such G must satisfy (from established claims).**

1. `G` is finitely presented, of type FP and torsion-free, with Wall class
   `σ(G) ≠ 0` (`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`).
2. `K̃_0(ZG) ≠ 0`. So `G` refutes Conjecture 1.3 of Lück–Reich and with it the
   K-theoretic Farrell–Jones conjecture, and lies outside every class where that
   conjecture is proved (`f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`).
3. For type-F groups `H`, `G × H` is of type F exactly when `χ(H) σ(G) = 0`
   (`g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class`). In particular
   `G × F_2` is not of type F.
4. `G` has no free cocompact action on an acyclic CW complex, since cellular chains
   would give a finite free resolution (type FL). Because `G` is torsion-free,
   proper means free, so `G` has no contractible Rips complex, and `G` also answers
   Problem 4.6 (`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`) negatively.
5. Through the routes landed by lane z1-21-type-f-proof between
   `hsiang-reduced-k0-of-torsion-free-group-rings-vanishes` and
   `reduced-k0-of-universal-fp-torsion-free-tester-vanishes` (unreviewed as of
   2026-09-13), `K̃_0(ZU) ≠ 0` for the one fixed finitely presented torsion-free group
   `U` of `higher-whitehead-universal-finitely-presented-torsion-free-group`.
   No torsion-free group with `K̃_0(Zπ) ≠ 0` is known (Ferry–Ranicki,
   arXiv:math/0008070, p. 5, read verbatim).

## Attempts

- **Projectives from finite subgroups.** `K̃_0(ZQ) ≠ 0` for many finite `Q`
  (Lück–Reich, Remark 1.4: `K̃_0(Z[Z/23]) ≅ Z/3`). Dead: `G` is torsion-free.
- **Wall realization.** Every class of `K̃_0(Zπ)` is the obstruction of some
  finitely dominated complex with fundamental group `π` (Wall 1965, not re-read).
  Dead as stated: those complexes are not aspherical.
- **Kan–Thurston lift** (z1-21-wall-obstruction, 2026-09-13). Suppose `X` is
  finitely dominated with `σ(X) ≠ 0` and `f : T → X` is an acyclic map from an
  aspherical finitely dominated `T`. Then `Zπ_1X ⊗ C_*(T̃)` computes
  `H_*(T; Zπ_1X) ≅ H_*(X̃)`, and a homology equivalence of bounded-below free complexes
  is a chain equivalence, so `f_* σ(T) = σ(X) ≠ 0` and `π_1 T` is a counterexample.
  Kan–Thurston and Baumslag–Dyer–Heller give aspherical `T` with acyclic maps, finite
  when `X` is finite. **Dies at finite domination of `T`.** A finitely dominated `X`
  is a telescope of a homotopy idempotent `p` of a finite complex, the construction
  is functorial only in strict maps, and nothing forces `T(p) ∘ T(p) ≃ T(p)`.
  Firewall: if `π_1 T` is a directed colimit of Farrell–Jones groups (as for
  telescopes of cubical Kan–Thurston models of finite complexes; Leary's metric
  Kan–Thurston theorem, not re-read), then `σ(T) = 0`, so no such `T` is finitely
  dominated over an `X` with `σ(X) ≠ 0`.
- **Screening groups outside the Farrell–Jones classes.** Candidates of finite `cd`
  and type `F_∞` to screen: Artin groups whose `K(π,1)` conjecture is open (their
  `cd` is not even known to be finite; see the Problem 1.5 lanes), torsion-free
  finitely presented groups from Higman-type embeddings, finite-`cd`
  small-cancellation constructions. Blocker: no method computes `K̃_0(ZG)` outside
  the Farrell–Jones classes, so no candidate has a known nonzero class.
