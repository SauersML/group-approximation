---
rg: 2
id: fpbs-kazhdan-local-cost-formula
kind: claim
title: For a Kazhdan group the Bernoulli cost is an infimum of window-local statistics of finite-range iid subgraphs, so fixed price one is a finite-certificate statement
distinct_from:
  fpbs-hp-condensation-bernoulli-exit: that is a dichotomy for the Hutchcroft--Pete recursion inside W_b and needs a positive-frequency cluster as input; here condensation is derived from a window-local defect below kappa^2 p for any subgraph, with no recursion and no hyperfinite coins, and the resulting bound has a matching converse.
  fpbs-kazhdan-ergodic-percolation-disagreement-floor: that floor is a window-0 statement at the scale of the density p; the certificate here uses cluster-counting fields over balls of radius R, and the floor does not bound its defect.
  fpbs-sparse-spine-cost-bound: that needs an FIID connected infinite vertex set, a global property; here the input is a subgraph that is only locally near-connected between neighbours, and property (T) supplies the global generation.
  fpbs-kazhdan-sparse-spines: that open target asks for sparse connected FIID spines; this claim gives an exact local formula for C(b_Gamma) whose value 1 is equivalent to fixed price one, with bond subgraphs on all vertices allowed.
---

**PROPOSED ESTABLISHED (written proof over imported theorems; see the proof route).**

**Setting.**
- `Gamma` is a countably infinite group with a Kazhdan pair `(S, kappa)`. `F` is a finite symmetric subset of
  `Gamma`, and `B_R` is the word ball of radius `R` for `S union F`.
- A *random subgraph* on a free ergodic p.m.p. `Gamma`-space `X` is a Borel equivariant map `x -> G_x = (V_x, E_x)`,
  with `V_x` a subset of `Gamma`, `E_x` a set of edges `{g, gf}` (`f` in `F`) between points of `V_x`, and
  `G_{gamma x} = gamma G_x`. Its density is `p = mu(e in V_x)`. Its clusters are the components of `G_x`.
- For a finite window `W` containing `B_R union s B_R` for all `s` in `S`, the *window defect* is
  `D_{R,W}(s) = E sum_K | |K cap B_R| - |K cap s B_R| | / |B_R|`, where `K` runs over the classes of
  `V_x cap (B_R union s B_R)` under "joined by a path of `G_x` inside `W`". It is the expectation of a cylinder
  function, so it is weak-star continuous in the law of `G`. For `R = 0` and `V = Gamma` it equals
  `2 P(e and s are not joined inside W)`.

**Theorem 1 (Kazhdan condensation with a cost bound).** Let `D = max_{s in S} D_{R,W}(s)`. If `D < kappa^2 p`, then
`G` has a nonempty equivariant finite set of clusters almost surely, those clusters cover a proportion
`u >= p - D/kappa^2` of the space, and
`C(X) <= 1 + E[(deg_G(e)/2 - 1) 1_{e in V}] + D/kappa^2`.

**Corollary 2 (Bernoulli transfer).** If `X` is free and weakly contained in `b_Gamma`, in particular if `G` is a
factor of iid, then `C(b_Gamma)` obeys the same bound.

**Theorem 3 (local formula).** `C(b_Gamma) = 1 + inf (E deg_G(e)/2 - 1 + 2 delta_W / kappa^2)`. The infimum runs over
finite `F`, finite windows `W`, and bond subgraphs `G` on `V = Gamma` that are finite-range, finite-alphabet
block factors of iid, with `delta_W = max_{s in S} P(e and s not joined inside W) < kappa^2/2`.

**Corollary 4 (quantifier shift).**
- Let `Gamma` have solvable word problem and a rational lower bound `kappa_0 <= kappa`. The quantity inside the
  infimum of Theorem 3 is an exact rational for block factors with rational weights. Replacing `kappa` by `kappa_0`
  keeps the formula exact. So `C(b_Gamma)` is a right-computably-enumerable real.
- By Abert--Weiss maximality, `Gamma` has fixed price one iff for every `eta > 0` some finite certificate
  `(F, W, block rule)` has `E deg/2 - 1 + 2 delta_W/kappa_0^2 < eta`.
- Equivalently, an infinite Kazhdan group has fixed price one iff, for every `eta > 0`, some Cayley graph carries a
  factor-of-iid subgraph with expected degree below `2 + eta` in which neighbours are joined inside a bounded window
  with probability at least `1 - kappa^2 eta/4`. Connectedness is replaced by window-local near-connectedness.

**Relation to the Hutchcroft--Pete gap.**
- `fpbs-hp-condensation-bernoulli-exit` reduces fixed price one for Kazhdan groups to condensation inside `W_b` at
  small density, and asks for a condensation theorem with hyperfinite-subrelation coins. Theorem 1 supplies
  condensation from a window-local, weak-star open inequality for any subgraph, with no recursion. Any `W_b` law
  meeting it can be replaced by nearby block factors, which also meet it.
- The ergodic disagreement floor blocks the Hutchcroft--Pete limit only at window `0` and at scale `p`. At `R = 0` a
  site certificate would need neighbour disagreement in `[kappa^2 p(1-p), kappa^2 p)`. For `R > 0` the defect
  compares cluster counts over balls, and the floor gives no lower bound for it.
- What remains open is the construction: finite-range iid subgraphs with degree near `2` and window defect near `0`.
  This is now a search over finite objects with a decidable acceptance test.

**Calibration.**
- Every accepted certificate must give a value of at least `1`. Mass transport confirms this: infinite clusters
  have mean degree at least `2`, and by Theorem 1 they carry mass `u >= 1 - 2 delta_W/kappa^2`, so
  `E deg/2 >= 1 - 2 delta_W/kappa^2`.
- The empty subgraph has `delta_W = 1 >= kappa^2/2`, so it is rejected, as it must be.
- Amenable groups and free groups have no Kazhdan pair, so the formula makes no claim there. On `Z`, deleting each
  edge independently with probability `epsilon` gives `V = Z`, `D = 2 epsilon + o(epsilon)` and only finite clusters.
  Theorem 1 would force `u >= 1 - D/kappa^2 > 0`, a contradiction for every `kappa > 0`. So the hypothesis is used
  essentially, and the theorem correctly detects that `Z` has no Kazhdan pair.
- For an infinite Kazhdan group, the full Cayley graph `G = Cay(Gamma, S)` has `D = 0` and gives `C(b) <= |S|/2`.
  The generating-graphing bound is recovered.
