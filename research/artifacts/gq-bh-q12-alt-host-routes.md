# Non-BBMZ F_∞ hosts for Kazhdan hyperbolic groups: routes checked (bh-q12-alt-host, 09-19)

Target: an `F_∞` simple host, not built from a BBMZ rational similarity group, for some hyperbolic
group with property (T). Result: `arithmetic-lattices-embed-in-f-infinity-simple-groups` covers every
lattice in `Sp(n,1)`, `n ≥ 2`, and in `F_4^{(-20)}`. The three routes in the brief are assessed below.

**Priority (added 09-19).** Llosa Isenrich–Schesler–Wu, arXiv:2510.01952, Theorem 1.4 and
Remark 1.5: every finitely generated `ℚ̄`-linear group embeds in a simple group with the same
finiteness properties. That already covers every `F_∞` lattice in `Sp(n,1)` and `F_4^{(-20)}`. The
landed node is an independent tree route with attribution to them. The quote came from a summarizing
fetch and was not read at source.

## Route (b): twisted Brin–Thompson SV_G with G = Γ is blocked

By `abstract-twisted-bt-type-fn-criterion` (refereed), `SV_G` is of type `F_∞` iff `G ↷ S` is of
type `[A_∞]`:
- `G` is of type `F_∞`;
- finite-set stabilizers are of type `F_∞`;
- the action is oligomorphic.

With `G = Γ` itself this runs into the following.

**Lemma (lane proof, not reviewed; likely folklore).** Let `Γ` be a non-elementary hyperbolic group
and `H ≤ Γ` a subgroup whose limit set `Λ(H)` is not all of `∂Γ`. Then `H\Γ/H` is infinite.

*Proof.*
1. **Choice of `γ`.** Pairs of fixed points of loxodromics are dense in `∂Γ × ∂Γ`, so some
   loxodromic `γ` has `γ^±` in the open set `∂Γ ∖ Λ(H)`.
2. **Bounded products.** `A = sup_{h∈H, n≥0} (γ^{-n}·h)_1` is finite. Otherwise `(γ^{-n_k}·h_k)_1 → ∞`
   along some sequence. Then `n_k → ∞`, so `h_k → γ^-`, which forces `γ^- ∈ Λ(H)`. Likewise
   `B = sup (γ^n·h)_1 < ∞`.
3. **Estimate.** For `x = γ^n h'` with `h' ∈ H`, `(x·γ^n)_1 = |γ^n| − (γ^{-n}·h')_1 ≥ |γ^n| − A`.
   For `h ∈ H`, `(h·γ^n)_1 ≤ B`. By `δ`-hyperbolicity, once `|γ^n| − A > B + δ` we get
   `(h·x)_1 ≤ B + δ`. So `d(h, x) ≥ |x| − 2(h·x)_1 ≥ |γ^n| − A − 2B − 2δ`.
4. **Conclusion.** `d(H, γ^n H) → ∞`. Now `d(H, gH) = min |h^{-1} g h'|` is constant on each double
   coset `HgH`, so there are infinitely many double cosets. ∎

**Consequences.**
- In any action of `Γ` with finitely many orbits on pairs, every stabilizer of a point in an
  infinite orbit has full limit set.
- A locally quasiconvex hyperbolic group, such as a free or surface group, has no action on an
  infinite set with finitely generated stabilizers and finitely many orbits of pairs. For a surface
  group, a finitely generated infinite-index subgroup is quasiconvex, so its limit set is proper.
- For a Kazhdan `Γ` the route would need an `F_∞` infinite-index subgroup with full limit set and
  finitely many double cosets. No such subgroup is known.

That is why hosts of this kind use a larger actor, such as the rigid permutation group of
Bux–Llosa Isenrich–Wu, rather than `Γ`.

## Route (c): rigid permutation groups (Bux–Llosa Isenrich–Wu) works for lattices

Theorem 11.1 needs a faithful member of `BS_Γ`. For arithmetic lattices one is landed and refereed
(`arithmetic-lie-lattices-have-faithful-bs-members`, commensurator letters plus Borel density).

The `F_n` form for every `n`, with one envelope, gives `F_∞`. All lattices in `Sp(n,1)` and
`F_4^{(-20)}` are arithmetic, and their cocompact members are hyperbolic and Kazhdan. So route (c)
answers the brief for that class; it is the landed node.

Its gate is residual finiteness. `𝓗_31` (Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276,
Theorem 1.2) and random groups are not known on main to be lattices or residually finite, so
neither is reached.

## Route (a): a non-BBMZ rational similarity group was not attempted

The obstruction in `bbmz-hosts-with-higher-dimensional-boundary-are-unbounded` concerns the
boundary action. A different RSG for `Γ` would still act on a Cantor model of `∂Γ` with no local cut
points. So there was no evident reason to expect the uncountable singular sets to disappear, and no
time was spent on this route.

## Open, sharpened

`F_∞` simple hosts for hyperbolic Kazhdan groups that are not known to be residually finite, such as
`𝓗_31` and random groups. The tree route needs residual finiteness and the BBMZ route needs bounded
singular sets, so each of these needs a new mechanism.
