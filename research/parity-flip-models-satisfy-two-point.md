---
rg: 2
id: parity-flip-models-satisfy-two-point
kind: claim
title: Locally additive transport parity yields exact two-point models
distinct_from:
  two-point-orbit-approximation: that asserts existence of two-point approximations at every window; this identifies a degenerate prover class — one-bit flip models — and shows it succeeds exactly at every window where the transport parity extends locally additively, which is what any refutation must first defeat.
  exact-models-cannot-separate-marked-pair: that kills genuine actions, whose multiplicativity is global; the flip models here are exactly multiplicative on the tested window pairs yet are not actions of G (the parity is not a homomorphism), which is why they slip through that theorem.
  pair-constraint-graph-criterion: that converts label data into component conditions for arbitrary models; this exhibits a specific two-element model where the components split for parity reasons alone.
---

Let `X` be a `G`-set, `p ≠ q ∈ X` a marked pair, and for `g ∈ G` define the
**transport parity** `τ(g) ∈ {0,1}`, partially: `τ(g) = 0` if `g` fixes
every element of `{p,q}` that it keeps inside `{p,q}` (and keeps at least
one), `τ(g) = 1` if `g` maps some element of `{p,q}` to the other.  (For
`g` with `g·p = q` or `g·q = p` set `τ = 1`; for `g` fixing `p` or `q`
without swapping set `τ = 0`; otherwise `τ` is undefined.  For the
Kun--Thom marked pair no window element can both fix one marked coset and
transport the other, so the two clauses never conflict.)

**Theorem.**  Let `F ⊆ G` be a finite window and suppose there exists
`P : G → ℤ/2` with

```text
P(g) + P(g') = P(gg')   for all g, g' ∈ F,      P = τ on F where τ is defined.
```

Then the two-point approximation of `two-point-orbit-approximation` holds
at `(F, ε)` for **every** `ε > 0`, exactly: take `A = ℤ/2`,
`φ(w) = flip^{P(w)}`, `S = A`, `B = {0,1}`, `j_s(p) = s`,
`j_s(q) = 1 − s`.

Conversely, every flip model — `A = ℤ/2` with each `φ(w)` a power of the
flip — that satisfies the two-point clauses at `(F, ε)` for some `ε < 1`
arises this way: on `A = ℤ/2` the normalized Hamming distance between
distinct permutations is `1`, so `(F,ε)`-multiplicativity forces exact
local additivity, and the equivariance clauses force `P = τ` on the
letters where `τ` is defined.

**Why this matters.**  Together with
`exact-models-cannot-separate-marked-pair`, this brackets the prover space
of `two-point-orbit-approximation` from both degenerate ends: genuine
actions fail (their multiplicativity is global and the collapse
`φ(h) ∈ φ(Γ)` kills them), while one-bit parity models succeed wherever
parity extends — so a refutation of the two-point claim must, at minimum,
work at windows where the transport parity is trapped.  Such a window
exists and is explicit: `parity-trap-window`.  The claim also calibrates
the definition itself: the two-point property at a FIXED window can be
carried by models with no geometric content whatsoever, and only the
`∀F` quantifier gives it strength.
