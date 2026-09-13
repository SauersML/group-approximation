---
rg: 2
id: lampshuffler-groups-are-not-fp2-over-q
kind: claim
title: "Lampshuffler groups FSym(X) x| G over a virtually indicable acting group are not of type FP_2 over Q"
distinct_from:
  houghton-h2-is-not-fp2-over-q: that is the single group FSym(Z) x| Z, Houghton's H_2; this is the general statement for FSym(X) x| G with X any free G-set with finitely many orbits and G virtually indicable, and it specialises to that one.
  every-countable-group-lies-in-a-faithful-ha2-actor: that asks for FP_2 overgroups with a faithful [HA_2] action; this is the theorem that one proposed family of candidates for such actors, the lampshufflers, never has the required finiteness.
  fp2-over-q-descends-along-locally-finite-kernels: that is the descent lemma for locally finite normal subgroups; this is a non-existence theorem about a specific family of locally-finite-by-G groups, and it reproves the one step of that lemma it uses.
artifacts:
  - research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md
---

**ESTABLISHED** by the complete proof in `lampshuffler-groups-are-not-fp2-over-q-proof`
and `research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md` (not independently
reviewed; review requested from z-verify-groups).

**Theorem A.** Let `G` be a group with a surjection `G -> Z`, let `X` be a set on which
`G` acts freely with finitely many orbits, and let `K = FSym(X)` be the group of
finitely supported permutations of `X`. Then `K x| G` is not of type `FP_2` over `Q`.

**Corollary B.** If `G` is finitely generated and some finite-index subgroup of `G`
surjects onto `Z`, then `FSym(X) x| G` is not of type `FP_2` over `Q`, hence not of
type `FP_2` over `Z`, and not finitely presented.

In particular the lampshuffler `Shuffler(G) = FSym(G) x| G` is not of type `FP_2` for
every finitely generated virtually indicable `G`: for `Z^d`, for free groups, for
one-ended right-angled Artin groups and surface groups, and for `G_L(S) x Z` with
`G_L(S)` one of Leary's groups.

**Mechanism.** Over `Q` a locally finite kernel is invisible, so `FP_2` forces
`H_1(K x| G; prod_I Q[K x| G]) = 0`. The five-term sequence of
`1 -> FSym(X) x| ker(G -> Z) -> K x| G -> Z -> 1` turns that into a statement about
`t`-invariants of coinvariants, and the invariant is realised by
`y_n = (1 + t + ... + t^(n-1)) (1 - s)(1 - s_n)`, where `s` is a transposition and
`s_n = t^(-n) s t^n` runs away from it. One averaging idempotent kills `(t-1)y`
uniformly in `n`; no single finite subgroup and no finite set of kernel elements kills
`y`, because a coset functional on `H \ (K x| G)` sees the coefficient `1` at level `i`
for suitable `i`. Freeness of the action is what makes the exceptional set of levels
finite, and it is exactly what fails for Houghton's `H_n` with `n >= 3`, which are
finitely presented.

**Credit.** For `G = Z, X = Z` this is Houghton's group `H_2` and the result is Brown's
(JPAA 44 (1987): `H_n` is of type `F_(n-1)` but not `FP_n`). The proof generalises this
repository's rational argument for `H_2` (`houghton-h2-not-fp2-over-q-proof`), reusing
its averaging-idempotent mechanism. Genevois-Tessera, arXiv:2401.13520 Theorem 1.5,
prove that lampshufflers over infinite groups are never finitely presented; this
strengthens that to `FP_2` in the virtually indicable range.

**Consequence for Zaremsky Problems 1.25 and 1.20.** The lampshuffler route to a
faithful `[HA_2]` actor is dead: `FSym(Γ) x| Γ` acts faithfully and highly transitively
on `Γ` with finitely generated point stabilisers, but it is never of type `FP_2` for the
`Γ` proposed (one-ended and virtually indicable, e.g. `G_L(S) x Z`), so it is not an
`FP_2` actor. See `every-countable-group-lies-in-a-faithful-ha2-actor`.

**Scope.** `G` with no infinite virtually free quotient at all (for instance a Kazhdan
group) is not covered; the `FP_2` status of `FSym(G) x| G` there is open, and the same
element is expected to work through any infinite virtually free quotient.

DERIVATION
lampshuffler-groups-are-not-fp2-over-q-proof
