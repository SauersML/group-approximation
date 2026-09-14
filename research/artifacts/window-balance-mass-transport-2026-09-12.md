# Window balance for injective automata: the fiber upper bound and where mass transport stops

Lane `w3-bern-window`, 2026-09-12. Supports `window-balance-is-a-fiber-upper-bound` and
`decoder-window-fiber-bound-loses-exactly-the-boundary`, and records an Attempts entry on
`every-injective-ca-preserves-uniform-bernoulli-measure`.

## 1. Setting

`G` is a group, `A` a finite alphabet with `q = |A| >= 2`, `mu` the uniform product measure on
`A^G`, and `tau` a cellular automaton with finite memory `M` containing `1` and local rule `mu_loc`:

    tau(x)(g) = mu_loc( (x(gm))_(m in M) ).

For a finite window `E`, the output on `E` reads the input on `EM`. Write
`tau_E : A^(EM) -> A^E` and, for `p in A^E`,

    c_E(p) = | tau_E^(-1)(p) | .

Then `tau_* mu (p on E) = c_E(p) q^(-|EM|)`, and `sum_p c_E(p) = q^(|EM|)`.

## 2. Balance is a pure upper bound

**Proposition 1.** For a fixed finite window `E` the following are equivalent:

1. `tau_* mu` restricted to `E` is uniform;
2. `c_E(p) = q^(|EM| - |E|)` for every `p in A^E`;
3. `c_E(p) <= q^(|EM| - |E|)` for every `p in A^E`.

Balance at `E` implies balance at every subwindow of `E`. So `tau_* mu = mu` exactly when (3)
holds on a cofinal family of windows, for instance on the balls of a word metric.

*Proof.* (1) iff (2) by the displayed formula. (2) implies (3) trivially. For (3) implies (2):
the `q^|E|` numbers `c_E(p)` sum to `q^(|EM|)`, so their average is `q^(|EM| - |E|)`, and a
family bounded above by its average is constant. Subwindows: marginals of a uniform law are
uniform, and a measure on `A^G` is determined by its cylinder values. QED

A Garden-of-Eden pattern is exactly a window where some `c_E(p) = 0`, and then (3) fails
somewhere else on `E`. So a proof of Gottschalk through balance only has to produce UPPER bounds
on fiber sizes; no lower bound is ever needed.

## 3. The decoder bound and its exact loss

Suppose `tau` is injective. By Curtis--Hedlund--Lyndon and compactness it has a decoder: a finite
`N` and a rule `nu_loc` with

    x(g) = nu_loc( (tau(x)(gn))_(n in N) )     for all x and g.

Enlarging `N` keeps this true, so take `1 in N`. For a finite window `E` put

    int_N E = { g in G : gN is contained in E },     d_N E = E \ int_N E .

**Proposition 2.** For every finite `E` and `p in A^E`,

    c_E(p) <= q^(|EM| - |int_N E|) = q^(|EM| - |E|) * q^(|d_N E|) .

*Proof.* Let `q_1, q_2` lie in the fiber of `p`, extended to configurations `x_1, x_2` by one
common exterior. For `g` in `int_N E`, every `gn` lies in `E`, so `tau(x_i)(gn) = p(gn)` for both,
and the decoder gives `x_1(g) = x_2(g)`. Injectivity of `tau` forces `1 in NM` (otherwise the
decoded value would not depend on `x(g)`), so `g in gNM` is contained in `EM` and the coordinate
`g` is one of the fiber's coordinates. So the fiber lies in a coset of the coordinates of
`int_N E`, which has `q^(|EM| - |int_N E|)` elements. QED

**Exact loss.** Against Proposition 1(3), the decoder bound is off by exactly the factor
`q^(|d_N E|)`, the number of patterns on the `N`-boundary of the window. Balance is the statement
that this factor can be removed.

**Calibration on amenable groups (classical).** If `p_0` on `Omega` is a Garden of Eden, translate
it so that `1 in Omega`. Every window `F` containing `k` disjoint translates of `Omega` has at most
`q^|F| (1 - q^(-|Omega|))^k` patterns with nonzero fiber. Proposition 2 forces at least
`q^(|int_N F|)` of them. A maximal disjoint family of translates `g Omega` inside `F` meets every
`g Omega` with `g in int_Omega F`, so `k >= |int_Omega F| / |Omega Omega^-1|`. With Folner windows
`|d_N F| / |F| -> 0`, this is a contradiction. That is Gromov--Weiss surjunctivity for amenable
groups, in fiber-count form. (Normalization and count as corrected by `w3-vf-positive`, Section 5 of
`research/artifacts/w3-vf-positive-verification-2026-09-12.md`.)

**Nonamenable groups.** For `N` containing a generating set of a nonamenable subgroup,
`inf_F |d_N F| / |F| > 0` (Folner criterion). The inequality

    |d_N F| log q  >=  k(F) * log( 1 / (1 - q^(-|Omega|)) )

then holds on every window once `|Omega|` is large, so the per-window count gives no
contradiction. Averaging over translates, or over invariant random windows (mass transport),
changes nothing: bijective translations fix totals and preserve the boundary density, and on a
nonamenable group that density is bounded below.

## 4. Which ingredient does what

The per-window relations available are:

* (a) totals `sum_p c_E(p) = q^(|EM|)` and translation invariance `c_(gE)(gp) = c_E(p)`, which is
  what unimodularity (bijective translations) supplies;
* (b) the decoder fiber bound of Proposition 2, which is injectivity;
* (c) zeros at Garden-of-Eden patterns, which is strictness.

The two landed calibrations each drop one of them:

* The end-fixing tree (`end-fixing-tree-symmetries-carry-strict-automata`) satisfies (b) and (c).
  The automaton copies the parent and is decoded from a child. It fails (a), since the parent map is
  two-to-one and the read and read-by counts differ.
* Pre-injective, non-surjective automata over nonamenable groups (Section 5) satisfy (a) and (c),
  but have no decoder and fail (b).

## 5. The pre-injective calibration (literature remark, not imported)

Bartholdi and Kielak (J. Eur. Math. Soc., 2019) show that every nonamenable group carries a
pre-injective automaton that is not surjective. The repository records this only as a remark
(`research/artifacts/measurable-alphabet-compression-2026-09-12.md`), so no node consumes it here.
If the statement is as recorded, such an automaton satisfies (a) and (c) and fails balance at some
window. So no argument built only from translation totals, finite memory and pre-injectivity can
certify balance on any nonamenable group. What injectivity adds beyond pre-injectivity is precisely
the uniform decoder, which is relation (b).

## 6. Conclusion

So the equation that needs more than unimodularity is exactly the boundary-free form of (b): for an
injective automaton, remove the factor `q^(|d_N E|)` on some cofinal family of windows. At the
single window `E = {1}` with `|N| >= 2`, `int_N E` is empty and (b) says nothing, so the first
equation of the family, the one-site upper bound `c_{1}(a) <= q^(|M| - 1)`, already carries the
whole problem.
