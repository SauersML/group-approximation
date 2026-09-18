---
rg: 2
id: leavitt-steinberg-thompson-extensions-add-nothing
kind: claim
title: Extending St_N(R_L) by Thompson's V through Leavitt unit twists, or by any ring symmetries, adds nothing for Boone–Higman; St_N(R_L) ⋊ V is St_N(R_L) × V, its only simple quotients are V and PE_N(R_L), it has no type (A) action, and every FW shell obstruction of St_N(R_L) survives
distinct_from:
  st-n-of-r-l-is-generated-by-two-copies-of-itself: that proposes the host St_N(R) ⋊ V from the tree of corner copies; this tests that host and shows it is St_N(R) × V, with every gate closed exactly as for St_N(R_L).
  steinberg-groups-of-r-l-are-quasisimple: that determines the simple quotients of St_N(R_L); this extends the verdict to every group containing St_N(R_L) as a normal subgroup.
  steinberg-leavitt-resolvent-groups-have-no-type-a-action: that excludes St_N(R_L) itself as a type (A) actor; this excludes every extension of St_N(R_L) by ring automorphisms or anti-automorphisms, and by the Leavitt copy of V.
  fw-inputs-fail-commuting-shell-windows: that closes commuting windows for FW shell groups; this carries the closure to shell groups K × H with Hom(K, H) = 1, which need not be FW.
---

**ESTABLISHED** through `leavitt-steinberg-thompson-extensions-add-nothing-proof`. Lane proof by gq-stv-host, elementary
given the cited nodes, not independently reviewed. Three inputs are recalled, not read at source:
- that Thompson's `V` is acyclic, in particular `H_2(V; Z) = 0` (Szymik–Wahl, arXiv:1411.5035);
- that `V` acts properly on a CAT(0) cube complex (Farley);
- that the product `K_1(Q) ⊗ K_1(R) -> K_2(R)` exists for a `Q`-algebra `R` (the `K_*(Q)`-module structure).
No priority is claimed.

**Setting.**
- `R_L` is the Leavitt resolvent ring, `N >= 3` (`N >= 4` wherever property FW is used), and `S = St_N(R_L)`.
- `V ≤ L_Z(1,2)^x ≤ R_L^x` is the standard copy of Thompson's group: the unitaries `Σ s_α t_β*` over bijections of
  complete prefix codes.
- For `u ∈ V`, `Σ^(u)` is the isometric twist of the last coordinate (`leavitt-stabilization-kernels-are-one-step`).
  For unitary `u` it is the automorphism of `S` covering conjugation by `D_u = diag(1, …, 1, u)`.
- The proposed host is `G = S ⋊ V` with `u` acting by `Σ^(u)`. Corner and scalar variants (conjugation by `u·I`, or by
  any `D(u) ∈ GL_N(R_L)` depending homomorphically on `u`) behave the same way.

**Statement.**
1. **Normal extensions add no simple quotients (general).** Let `K` be a group with a unique simple quotient `K̄`, for
   example a quasisimple group. If `K` is a normal subgroup of any group `H`, then every simple quotient of `H` either
   kills `K` or is isomorphic to `K̄`.
   - For `K = St_N(R_L)`, `K̄ = PE_N(R_L)`, which is not finitely presented.
   - So no group containing `St_N(R_L)` as a normal subgroup has a finitely presented simple quotient in which
     `St_N(R_L)` survives. That covers semidirect products with any group acting by any automorphisms, and central or
     other extensions.
2. **Acyclic inner actions split off (general).** Let a group `H` with `H_1(H) = H_2(H) = 0` act on a group `K` by
   inner automorphisms. Then `K ⋊ H ≅ K × H`.
3. **The proposed host.** `G = St_N(R_L) ⋊ V ≅ St_N(R_L) × V`. Hence:
   - (a) **No new simple quotients.** The simple quotients of `G` are `V` and `PE_N(R_L)`. The only one in which
     `GL_n(Q)` survives is `PE_N(R_L)`, and it is not finitely presented.
   - (b) **No type (A) action.** `K_2(N, R_L) ≅ Q^x` is central in `G`, so `G` has no faithful action with finitely
     many orbits on two-element subsets. More generally, let `Γ` be any group acting on `S` through ring automorphisms
     and anti-automorphisms of `R_L`, together with Leavitt twists. Then `Γ` acts on `K_2(N, R_L)` through `±1`. So in
     `S ⋊ Γ` the infinite subgroup `K_2(N, R_L)` has a centralizer of index at most 2, and `S ⋊ Γ` has no type (A)
     action.
   - (c) **The FW shell obstructions survive.** Let `P = K × H` with `K` infinite, finitely generated and FW, and
     `Hom(K, H) = 1`, and take any genuine action of `P` with infinite supports. Every shift-power normalization
     `s^∓m ρ(P) s^±m ≤ ρ(P)` restricts to the same normalization of `K`. Every commuting window of `P` reduces, by the
     mechanism of `fw-inputs-fail-commuting-shell-windows`, to such a normalization of `[P, P] ⊇ K`, which again
     restricts to `K`. So:
     - ascending window zero fails for every shift power and every twist;
     - commuting windows fail in the ascending direction;
     - if `Z(K)` has infinite exponent, descending window zero fails for every shift power, and descending commuting
       windows fail.

     For `P = G`, `Hom(St_N(R_L), V) = 1`. The open window cases of `G` are therefore exactly those of `St_N(R_L)`:
     non-commuting windows `N >= 1`.
4. **Matrix size is irrelevant (remark).** `R_L^n ≅ R_L` as modules, so `GL_n(R_L) ≅ R_L^x`. The Whitehead embedding
   `u ↦ diag(u, u^-1, 1)` puts `R_L^x` in `E_3(R_L)` missing the scalars. So every `GL_n(Q)`, all `n` at once,
   embeds in the single simple group `PE_3(R_L)`, not only in `PE_10(R_L)`.

## Lesson for general BH

**Symmetry that lives inside the input is invisible to Boone–Higman.**
- **Inner symmetry.** Over a Leavitt ring, Thompson-type self-similarity (the corner-copy tree, and the copy of `V`
  among the units) is implemented by units of the ring, hence by inner automorphisms of `GL_N`. An acyclic group
  acting innerly splits off as a direct factor (item 2), so it cannot move the input's centre, cannot create a simple
  quotient, and cannot evade the FW shell obstructions (item 3c).
- **Extensions in general.** Any group containing a quasisimple input `K` as a normal subgroup has only the simple
  quotient that `K` already has (item 1).
- **Design rule for a finitely presented simple host.**
  - The host must contain `K` **non-normally**.
  - Inside the host, `Z(K)` must acquire infinitely many conjugates
    (`type-a-actors-have-no-infinite-virtually-central-subgroup`).
  - So the host's dynamics must genuinely move `K`'s centre. Ring symmetries act on `K_2(R_L) = {Q^x, N+1}` by `±1`
    and fix the scalars, so they never do. Neither semidirect products by them nor products with `V` can work.
- **For `GL_n(Q)` (BBMZ 5.3(5)).** This closes every "St_N(R_L) plus symmetries" design. What is left is an
  amalgam, HNN or full-group host in which the central `Q^x` is conjugated by elements outside every ring-induced
  automorphism, for instance an element acting on `Q^x` by a prime shift. That is the scale-shift gate.
- **In characteristic `p`.** The same analysis explains why characteristic `p` is different: with a Leavitt pair,
  `PE_N(R)` is a single host for all `GL_n(R)` at once (item 4). By `projective-elementary-fp-kernel-criterion` it is
  finitely presented once `K_2(N, R)` and the scalars are finitely generated. That fails for every ring containing
  `Q`, and can hold when the prime subring is finite.
