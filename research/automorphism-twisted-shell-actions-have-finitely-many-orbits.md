---
rg: 2
id: automorphism-twisted-shell-actions-have-finitely-many-orbits
kind: claim
title: If the shift twists a genuine shell action by an automorphism, all but finitely many points lie in finitely many infinite orbits
distinct_from:
  twisted-genuine-shell-actions-pass-both-germ-gates: that shows twisted actions pass both germ gates; this is a structural constraint on which actions can be twisted, when the twist is an automorphism.
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes the regular action of a one-ended input (a single one-ended orbit); this constrains every genuine action with an automorphism twist to finitely many orbits.
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

**ESTABLISHED** (lane proof below; elementary; not independently reviewed; no novelty claimed).

**Statement.** Let `P`, `S`, `rho`, `s` be as in `twisted-genuine-shell-actions-pass-both-germ-gates`,
with `phi` an automorphism of `P` and `s^-1 rho(g) s = rho(phi(g))` near infinity for `g in S`.
Then there are finitely many infinite `P`-orbits `O_1, ..., O_k` whose union is cofinite in `N`.

**Proof.** Write `f = s`. The relation gives `f rho(g) f^-1 = rho(phi^-1(g))` near infinity, so both
`f` and `f^-1` twist the action. Let `E` be the finite set of points where one of the finitely many
relations for `g in S ∪ S^-1` (for `f` or `f^-1`) fails, together with `0`.

- *Orbit map.* The Schreier graph of `rho` (generators `S`) has bounded degree, so deleting the edges
  at `E` splits the orbits meeting `E` ("touched" orbits, finitely many) into finitely many pieces and
  leaves every other orbit intact. `f` maps each piece, and each untouched orbit, into one orbit; so
  does `f^-1`. Hence on untouched orbits whose images are untouched, `f` induces an injective map
  `sigma` with `f(O) = sigma(O)` exactly, so `|sigma(O)| = |O|`.
- *Single ray.* `N = {f^n(0)}`, and every subset `A` with `f(A) Δ A` finite is finite or cofinite.
- *Finite orbits.* Let `Z` be the union of finite orbits and `Y` that of infinite ones. `f` maps
  `Y` into `Y` and `Z` into `Z` up to finitely many points, since pieces of touched orbits are
  finitely many and untouched orbits keep their size. So `Z` is finite or cofinite. If `Z` is
  cofinite, take an untouched finite orbit `O` with `|O| >= 2` visited after the ray has left `E`
  for good. Two visits `f^n(0), f^m(0) in O` give `sigma^(m-n)(O) = O`, so `f^(m-n)` permutes the
  finite set `O`, and the ray has a periodic point. So all but finitely many finite orbits are
  points, and `rho(P)` has finite supports: a contradiction. Hence `Z` is finite.
- *Finitely many infinite orbits.* Each touched orbit has finitely many out- and in-neighbours in
  the orbit graph. An untouched infinite orbit is visited infinitely often. Consider its `sigma`-chain.
  - If the chain avoids touched orbits and their neighbours, it is a `sigma`-cycle or a bi-infinite
    chain, and the union `A` of its orbits satisfies `f(A) = A` up to one point. So `A` is cofinite.
    On a bi-infinite chain, `f` maps each orbit onto the next, so the ray meets each orbit of the chain
    at most once after entering it, which is impossible for infinite orbits. So the chain is a cycle
    and consists of finitely many orbits.
  - Otherwise the orbit lies on a `sigma`-chain starting at an out-neighbour of a touched orbit. If
    that chain never returns to a touched orbit, the ray takes it at most once, which again visits
    each orbit once. So the chain returns, and there are finitely many such finite chains.
  In both cases only finitely many infinite orbits occur.

**Scope.** Endomorphism twists that are not automorphisms are not covered. Nothing is said about the
ends of the orbits. The one-ended regular case is `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`;
whether every orbit must have at least two ends is open. The `Z^2` example of
`eventually-periodic-genuine-shell-actions-give-fp-envelopes` has two two-ended orbits.
