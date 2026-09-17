---
rg: 2
id: modular-transport-imbalance-is-not-a-strictness-index
kind: claim
title: On the end-fixing tree the transport ratio 2 is the host's modular function along the decoder, not an index of strictness
distinct_from:
  injective-ca-random-order-transport-identity: that is the unweighted transport identity on groups, with the tree ratio 2 as a calibration; this proves the modular-weighted identity on the tree for every injective automaton and shows the unweighted ratio takes the values 2, 1, 4/5, 6/5 independently of strictness.
  injective-ca-random-order-transport-is-dominated: that is the open domination inequality on groups; this supplies tree calibrations of it (bijective shear up violates the unweighted form, the skewed kappa violates the modular-weighted form) and records no progress on groups.
  end-fixing-tree-symmetries-carry-strict-automata: that constructs the strict automaton; this computes its transport, groupoid cocycle and operator-algebra indices and shows none of them detects strictness.
  site-pullbacks-strict-iff-stabilizer-self-compressed: that classifies strict one-site maps by an index-[K : c^-1 K c] self-compression; this shows that site index is the only finite index in sight and is 1 over every group for every automaton.
  measure-conjugacy-invariants-cannot-certify-surjectivity: that kills invariants of the output measure up to conjugacy; this kills modular cocycles and Jones-type indices of the induced endomorphism, which are invariants of the host and of the decoder orientation.
artifacts:
  - research/artifacts/modular-index-calibration-2026-09-17.md
  - experiments/modular-index-calibration-2026-09-17/tree_transport.py
  - experiments/modular-index-calibration-2026-09-17/tree_transport.out
  - research/artifacts/modular-transport-imbalance-is-not-a-strictness-index-proof-attempt-2026-09-17.md
---

Let `T` be the 3-regular tree with a fixed end `xi`, `Gamma = Aut(T, xi)`, `h` the Busemann height toward `xi`, and
for vertices `u, o` let `(a, b)` be the type of `u -> o` (up `a` steps to the meet of the rays to `xi`, down `b`
steps). For an equivariant injective automaton `kappa` with an equivariant finite decoder memory `D`, `x` uniform,
`y = kappa(x)`, `U` i.i.d. order labels, put `t(u, w) = I(x(u); y(w) | y(D(u) ∩ past(w)), U)`,
`out(o) = sum_(w in D(o)) t(o, w)` and `in(o) = sum_(u : o in D(u)) t(u, o)`.

1. **Modular mass transport.** For every diagonally invariant `F >= 0` on `V x V`,
   `sum_w F(o, w) = sum_u F(u, o) 2^(b - a)`. So the rooted-configuration groupoid of `Gamma ↷ (A^V, lambda)` has
   Radon-Nikodym cocycle `2^(h(u) - h(o))` for **every** invariant probability `lambda`, independent of any automaton;
   over a group it is `1`.
2. **Weighted identity.** For every such `kappa`, `out(o) = log |A_in| = sum_(u : o in D(u)) t(u, o) 2^(b - a)`. The
   unweighted `in(o)/out(o)` is the transport-weighted mean of `2^(h(w) - h(o))` over the decoder arrows `o -> w`.
3. **The ratio is not a strictness index** (exact, `A = Z/q`):
   - strict copy-parent `tau`, decoder `min` over children: `out/in = 2`;
   - strict product `tau x shear up` on `A x A^2`: `out = in = 3 log q`, ratio `1`;
   - bijective shear up `(x1(v), x2(v) + x1(p v))`: ratio `4/5`, and `in = (5/2) log q > 2 log q = H(y(o))`, so the
     unweighted domination inequality fails on the tree for a bijective automaton;
   - bijective shear down `(x1(v), x2(v) + x1(c) + x1(c'))`: ratio `6/5`.
4. **Operator-algebra indices.** `mu(tau A^V) = 0`, so `f -> f o tau` is not defined on `L^inf(A^V, mu)` (not
   normal). For `q = 3` the symmetric decoder `sigma(y)(w) = 2(y(c) + y(c')) mod 3` preserves `mu` and its image
   subalgebra has infinite Pimsner-Popa index; for even `q` no symmetric two-child decoder is balanced. The only
   finite index `2` is on the site algebra, `l^inf(V)` over `f o p`, equal to `Delta(c) = [K : c^-1 K c]`; over a
   group every equivariant site map is bijective and this index is `1` for every automaton.
5. **Where strictness shows.** For the skewed injective (hence strict) automaton `kappa` of
   `finite-left-inverse-identity-does-not-force-balance` with `q = 2`, the weighted in-mass is `2` bits while
   `H(y(o)) = 1.9056...` bits: the modular-weighted domination inequality fails on the tree.

Consequently each of the four candidate forms of "strictness forces a nontrivial modular cocycle; unimodularity forces
it trivial" (host groupoid cocycle, unweighted ratio, weighted ratio, Jones or Pimsner-Popa index of the induced
endomorphism) fails at the first step: strictness does not force the cocycle or index to be nontrivial. After the
modular correction the tree's strictness sits in the domination step, so a proof of
`injective-ca-random-order-transport-is-dominated` must use `Delta = 1` (or freeness) inside the domination argument,
not only in the identity.

Artifact Sections 1 to 5; the script recomputes every transport term by exact enumeration and checks items 2 and 3.

## Attempts

- 2026-09-17 `a-gs-modular-index`: candidate direct proof (artifact Sections 1 to 5, script `tree_transport.py`),
  held OPEN. The route was withdrawn to
  `research/artifacts/modular-transport-imbalance-is-not-a-strictness-index-proof-attempt-2026-09-17.md`.
  * **Referees: all three lenses refuted one step.** Item 4 and the "Consequently" paragraph say candidate 4 (the
    Jones / Pimsner-Popa index of the induced endomorphism) fails at P1, "strictness forces a nontrivial index". The
    note shows no strict automaton with index `1`. In the only computed case the balanced left inverse `sigma` of
    the strict `tau` (`q = 3`) has **infinite** index, which is `!= 1`, so it supports P1 there. The index is 1 for
    bijective automata (`sigma = kappa^-1`). The other cases leave the index undefined (`tau^*` not normal; even `q`
    with symmetric two-child decoders only), so P1 is vacuous there, not false.
  * **Unproved universals.** "The only finite index is the index-2 site inclusion on `l^inf(V)`" is shown only for
    three constructions; decoders reading larger or asymmetric windows are not treated. The artifact line "P2 holds
    for each candidate" is the goal itself for candidate 4. Minor: the artifact says the Corollary 3 mean is `1/2`
    exactly when all transport goes to children; mixtures (2/3 grandchild, 1/3 self) also give `1/2`.
  * **Verified by every referee.** Items 1 (orbit counts `N(a,0)=1`, `N(0,b)=2^b`, `N(a,b)=2^(b-1)`, modular
    mass transport), 2 (chain rule, weighted identity), 3 (ratios `2`, `1`, `4/5`, `6/5`; bijective shear up gives
    `5/2 > 2`) and 5 (`kappa`, `2 > 1.9056` bits); the script reproduces `tree_transport.out`.
  * **Fix.** Limit the conclusion to candidates 1 to 3, and say that candidate 4 fails on finiteness (no finite,
    automaton-dependent index `2` among the constructions examined) or at P2, not at P1; or exhibit a strict
    automaton with a balanced left inverse whose pullback has index `1`.
