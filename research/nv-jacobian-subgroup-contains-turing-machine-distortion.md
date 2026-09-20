---
rg: 2
id: nv-jacobian-subgroup-contains-turing-machine-distortion
kind: claim
title: "The Jacobian subgroup M_2 of 2V is the group of reversible Turing machines RTM(2,1), so every M_n (n >= 2) contains a Callard--Salo distortion element; no commensurating action is proper on M_n, and the fibre half of the Jacobian split is forced non-cubical"
distinct_from:
  nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal: that identifies M_n as the Lebesgue-preserving subgroup and M_2 as a groupoid full group, and leaves open ("not checked here") whether the Callard--Salo distortion element can be put inside M_2; this identifies M_2 with Callard--Salo's moving-tape group RTM_fix(2,1) and so puts a distortion element in M_2
  brin-thompson-mv-contains-a-distortion-element: that imports a distortion element of mV, which the Lemma 6.4 embedding with codes of unequal lengths need not place in the measure-preserving subgroup; this places one in M_n, and draws the consequence for the M_n-half of the Jacobian split
  full-shift-topological-full-group-is-a-t-menable: that is the Haagerup question for [[X]] < M_2; this is about the larger group M_2 = RTM(2,1) and shows it has a distortion element
  free-rewritable-tape-layers-kill-finite-presentation: that mentions M_2 = RTM(2,1) in a parenthetical comparison with no proof and no use; this proves the identification and uses it
  brin-thompson-nv-no-cubical-action-proper-on-cocycle-kernel: that forces P3 (properness on K) non-cubical through an elliptic conjugator; this forces properness on the larger subgroup M_n non-cubical through a distorted element, which cannot lie in K because K is torsion
  cubical-coset-proper-actions-capture-distorted-elements: that is the abstract bounded-or-linear and capture lemma; this supplies the distorted element inside M_n to which it is applied
---

**ESTABLISHED** by `nv-jacobian-subgroup-turing-machine-distortion-proof`.

## Setting

Notation of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`: `nV` acts on `C^n`, `c` is
the exponent cocycle, `K = ker c`, `M_n = {g : Σ_i c(g)_i ≡ 0} = {g : g_*λ = λ}` is the Jacobian
subgroup, `D ≅ V_{2^n,1}` is the diagonal subgroup, `X = {0,1}^Z`, and
`Φ(a, b) = … b_1 b_0 . a_0 a_1 …`.

Callard–Salo (arXiv:2208.00685v2, Section 6.2–6.3) write `RTM(n,k)` for the group of reversible
Turing machines with `n` tape symbols and `k` head states (their Definition 6.1), and
`RTM_fix(n,k)` for the same group in the moving-tape model (their Definition 6.2). For `k = 1` the
state set is a point, so `RTM_fix(2,1)` is a group of homeomorphisms of `X`.

## Statement

1. **Identification.** `Φ M_2 Φ^{-1} = RTM_fix(2,1)` as groups of homeomorphisms of `X`. Hence,
   by Callard–Salo Lemma 6.3, `M_2 ≅ RTM(2,1)`.
2. **Distortion in the Jacobian subgroup.** For every `n ≥ 2` there are a finitely generated
   subgroup `L ≤ M_n` and an element `f ∈ L` of infinite order with `|f^N|_L = O(log^4 N)`.
   - `f ∉ K`, and no power `f^d` with `d ≥ 1` lies in `D`. (`f^d ∈ D ∩ M_n = K` would make `f^d`
     torsion, because `K` is locally finite.)
3. **Class-kill.** No commensurating action of `M_n` is proper, for any `n ≥ 2`. In particular no
   commensurating action of `nV` is proper on `M_n`. This covers every action on a CAT(0) cube
   complex or on a discrete wall space. More precisely, in every commensurating action of `nV` the
   length `ℓ(f^N) = |f^N A Δ A|` is bounded in `N`.
4. **Forced shape.** For every cnd function `ψ` on `nV` (or on `M_n`), `ψ(f^N) = O(log^8 N)`. If
   `ψ` is proper on `M_n`, then `ψ(f^N) → ∞`. So every witness of the fibre half
   "some cnd function on `nV` is proper on `M_n`" (item 5 of
   `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`) is unbounded but at most
   polylogarithmic along `⟨f⟩`.
5. **Both halves of the Jacobian split are non-cubical.** By item 5 of
   `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, `nV` is Haagerup iff (Q_J) holds and some
   cnd function on `nV` is proper on `M_n`. Item 6(a) there makes (Q_J) non-cubical, and item 3
   here makes the second half non-cubical.
6. **Necessary prerequisite.** The goal `brin-thompson-groups-nv-are-a-t-menable` implies that
   `RTM(2,1) ≅ M_2` is Haagerup. This is recorded as `turing-machine-group-rtm-2-1-is-a-t-menable`
   (OPEN), via the route `turing-machine-group-rtm-2-1-a-t-menable-from-nv`. It sits in the chain
   `[[X]] ≤ M_2 ≅ RTM(2,1) ≤ 2V`. It is strictly more than the `[[X]]` prerequisite in one checkable
   sense: it contains a distortion element, so no cubical or wall proof reaches it.

## Why it matters

- **It answers the recorded open question.** `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`
  ends with: "Whether the Callard–Salo distortion element of 2V can be conjugated into `M_2` is not
  checked here." It can. Theorem D applied to `RTM(2,1)` gives a distortion element that lies in
  `M_2` by construction. No conjugation is needed.
- **It closes the cubical door on the fibre half.** Item 6(c) of that node exhibits the Maharam
  half-space as a commensurated measured wall on `M_n` whose cnd function `ψ_M` is unbounded. That
  suggested a cubical or wall-space attack on "proper on `M_n`". Item 3 kills every discrete wall
  or commensurating version of it. Along `⟨f⟩` the measured wall `ψ_M` itself is subadditive on
  `M_n`, so `ψ_M(f^N) = O(log^4 N)`.
- **Invariant and death step.** The invariant is sublinear word growth along `⟨f⟩ ≤ M_n`. Every
  commensurating candidate dies at the bounded-or-linear dichotomy (item 1 of
  `cubical-coset-proper-actions-capture-distorted-elements`). Sublinear growth forces `ℓ(f^N)` to be
  bounded, and then the infinitely many distinct `f^N` sit in one sublevel set.

## Not claimed

- That `M_n` for `n ≥ 3` is a Turing-machine group.
- That every `RTM(n,k)` embeds in `M_2`. Callard–Salo's Lemma 6.4 embedding uses codes whose word
  lengths need not be equal, so it need not preserve `λ`.
- Anything about whether `f` is conjugate into `[[X]]`.
- Any lower bound on `ψ(f^N)` beyond `→ ∞` for a proper `ψ`.
