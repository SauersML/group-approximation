---
rg: 2
id: shell-germ-quotient-algebra-fp-forces-fp-local-algebra
kind: claim
title: If the essential quotient A_nu/J of a shell germ algebra is finitely presented, then the local algebra K[Q]/J_p at the singular point is finitely presented, and every action locally modelled on the Schreier boundary is an action of the germ group
distinct_from:
  shell-germ-algebra-fp-forces-fp-germ-group: that starts from finite presentation of A_nu and ends with a finite presentation of the group Q; this starts from finite presentation of A_nu/J, the version the Boone--Higman route needs, and ends with a finite presentation of the algebra K[Q]/J_p, which is weaker.
  shell-germ-singular-ideal-is-generated-at-the-singular-point: that reduces finite GENERATION of J to finite generation of J_p in K[Q]; this derives finite PRESENTATION of K[Q]/J_p from finite presentation of A_nu/J, with no hypothesis on A_nu.
  shell-germ-algebra-fp-forces-bounded-germ-presentation: that reads bounded group relations of Q off a presentation of A_nu; this reads a finite presentation of K[Q]/J_p off a presentation of A_nu/J.
---

**ESTABLISHED** by `shell-germ-quotient-algebra-singular-ball-proof` (lane proof, elementary,
not reviewed; no priority claimed).

## Statement

Let `K` be a field, and let `A = A_K(G_nu)`, `J`, `Q`, `τ`, `r_g`, `M = K^N/K^(N)` and
`J_p = Ann_(K[Q])(M)` be as in `shell-germ-singular-ideal-is-generated-at-the-singular-point`.
Let `F = F(τ, S)`, and let `𝓛` and `X = ⊔_(H ∈ 𝓛) Q/H` be the Schreier boundary of
`shell-germ-singular-ideal-is-the-boundary-annihilator`. Suppose `A/J` is finitely presented.

1. **Local algebra.** `Λ_nu = K[Q]/J_p` is finitely presented as a `K`-algebra. More precisely,
   there is a finite set `E_0 ⊆ K[F]` with `Λ_nu = K[F]/(E_0)`. `Q` embeds in `Λ_nu^×`, because
   a nontrivial germ moves infinitely many shells and so acts nontrivially on `M`.
2. **Local rigidity of the boundary.** Let `ℓ` bound the lengths of the words in `E_0`. Let `Y`
   be any `F`-set such that every rooted `ℓ`-ball of its Schreier graph (generators `τ`, `S`)
   is isomorphic to a rooted `ℓ`-ball of `X`. Then `K[Y]` is a `Λ_nu`-module. In particular the
   `F`-action on `Y` factors through `Q`.

For `J = 0` the same proof gives `shell-germ-algebra-fp-forces-fp-germ-group`.

## What it changes

- **The escape is precisely located.** By `shell-germ-algebra-fp-forces-fp-germ-group`, the route
  `boone-higman-via-germ-steinberg-algebra-presentation` cannot pass through finite presentation
  of `A_nu` without finite presentation of `Q_nu`. What remains is `A_nu/J` finitely presented
  with `A_nu` not. Item 1 says that this needs `Λ_nu` finitely presented, and the group
  relations of `Q_nu` may then follow from algebra relations. This is the
  characteristic-2 mechanism of Attempt 2 on `shell-germ-algebra-fp-forces-fp-germ-group`.
- **The near-action obstacle is removed.** "The expected proof" on
  `shell-germ-algebra-fp-forces-fp-germ-group` was stuck because `Q` acts on `N` only as a
  near action. Item 2 moves the test to `X`, on which `Q` acts genuinely. **To refute finite
  presentation of `A_nu/J` for a given `nu`, it suffices to build, for every `ℓ`, an `F`-set
  that is `ℓ`-locally `X` on which some relation of `Q` fails.**
- **Generic shells pass that test.** For a generic `nu` and a finitely presented `P`, every
  `F`-set that is `ℓ`-locally `X`, with `ℓ >= 2` and `ℓ` at least the relator length of `P`, is
  a `Q_gen`-set killed by `J_p = ω(F_e)ω(F_o)K[Q]`.
  - **Parity is local.** A point is odd iff `S` fixes it. `τ` alternates parity, `P` preserves it,
    and odd points are fixed by `P`. All three are visible in `2`-balls.
  - **The parity-wreath relations follow.** Hence `τ^D P τ^(-D)` (`D` odd) moves only odd points,
    and `P` only even ones, both preserving parity.
    - This forces `[P, τ^D P τ^(-D)] = 1` on every point.
    - It also forces `(1 - a^(i))(1 - b^(j)) = 0` for `i` even and `j` odd.
  - **So the test cannot separate.** Although `Q_gen` is not finitely presented
    (`generic-shell-germ-algebras-are-not-finitely-presented`), permutation modules cannot
    show that `Λ_gen` is not finitely presented. Whether `Λ_gen` is finitely presented is open.
    It would be if the parity projection of `K[X]` were in `Λ_gen`: then
    `(1 - g) e = 0`, `e (1 - g) = 0` and `τ e τ^(-1) = 1 - e` would imply every
    `(1 - g)(1 - τ^D h τ^(-D)) = 0`.
