---
rg: 2
id: leavitt-primitive-corner-recursive-extension
kind: claim
title: A primitive subcorner carries a copy of the whole evaluation extension
distinct_from:
  leavitt-corner-idempotent-unital-surjection: that builds the corner `eAe` and its unital surjection onto `R`; this halves that corner to a primitive subcorner `fAf`, builds the corresponding surjection, and adds the thing that node has no analogue of — an embedding of the whole extension back into the subcorner.
  leavitt-matrix-amplification-in-unit-group-algebra: that puts matrix algebras over `S` inside `S`; this puts the evaluation *extension* `S ->> R` inside its own corner extension, compatibly with both maps, and the compatibility is the point.
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the evaluation map from the whole group algebra; this is a second, independent surjection onto the same `R` from a corner of augmentation zero, and it is the one that receives the recursion.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

Let `S = F_2[G]`, `G = L_(F_2)(1,2)^x`, `pi : S ->> R` the evaluation,
`e = [g] + [g^2]` the idempotent of
`leavitt-corner-idempotent-unital-surjection`.  Put

    f = [1] + [u] + [v] + [g],      T = f S f.

Then `f^2 = f`, `f <= e`, `eps(f) = 0`, `pi(f) = s_0 t_0`, and

1. `rho : T -> R`, `rho(a) = t_0 pi(a) s_0`, is a **surjective unital** ring
   homomorphism, `rho(f) = 1_R`;
2. `lambda : S -> T`, `lambda(a) = delta_*(a) f`, is an **injective** ring
   homomorphism with `lambda(1) = f`, where `delta_*` is induced by the scalar
   self-similarity `delta(q) = s_0 q t_0 + s_1 q t_1`;
3. `rho . lambda = pi`.

So the extension `S ->> R` reappears, verbatim and compatibly, inside the
corner extension `T ->> R`.  In particular `lambda(ker pi) <= ker(rho) = f K f`
with `K = ker(pi)`, and the corner kernel contains an injective copy of the
whole kernel.

## Why the *primitive* corner and not `eAe`

Because `e S e` is `M_2` of it.  The four matrix units `f_ij` of
`leavitt-matrix-amplification-in-unit-group-algebra` give a Peirce
isomorphism `Psi : eSe -> M_2(T)`, `Psi(x)_ij = f_1i x f_j1`, under which the
corner evaluation becomes `M_2(rho)`:

    Phi . pi|_(eSe) = M_2(rho) . Psi,        Phi(r)_ij = t_i r s_j,

because `rho(f_1i x f_j1) = t_i pi(x) s_j`.  Hence

    ker(pi|_(eSe)) ~= M_2(ker rho),      ker(rho) = f K f.

So nothing is lost by descending to `f`, and the object one has to understand
is one quarter the size.

## What it settles and what it does not

It settles that the corner kernel is not small: it contains `lambda(K)`, an
injective copy of a kernel already known to be nonzero
(`leavitt-evaluation-kernel-hits-augmentation-one`).  That is the input to
`leavitt-corner-kernel-not-jacobson-radical` and
`leavitt-recursive-kernel-idempotents`.

It does not produce a one-sided inverse, and the reason is worth recording
because the construction looks as if it should.  `rho . lambda = pi` invites a
recursive correction of an error term, `error -> lambda(error) -> lambda^2(error)
-> ...`; telescoping through depth `m` cancels the first `m` terms and leaves a
tail proportional to `lambda^m(error)`, nonzero for every `m` because `lambda`
is injective.  Group-algebra elements have finite support, so no infinite sum
is available to absorb the tail.  This is a genuine failure of the swindle,
not an unfinished computation.

Two further shortcuts are also closed.  Compressing `T` back to `eSe` by a
Murray--von Neumann equivalence is now isolated as the exact open claim
`leavitt-e-f-murray-von-neumann-equivalence`: it would produce the desired
direct-finiteness failure because `f<e` and both have augmentation zero.  The
augmentation blocks equivalence with `1`, but does **not** block `e~f`; no
proof or refutation of that equivalence is known.  And the set-theoretic
surjectivity witness `r |-> f [h_r] f`,
`h_r = Theta_2 [[r,1],[1,0]]`, is neither additive nor multiplicative; it
witnesses that `rho` is onto and nothing more.
