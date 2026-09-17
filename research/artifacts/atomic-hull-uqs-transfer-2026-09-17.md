# Strict designs on the atomic IRS hull transfer through uniform deficits (w5-gs-heretic, 2026-09-17)

Lane: counterexample direction on `gottschalk-surjunctivity-conjecture`, heretic role. This starts where
Wave 4 stopped on the transfer step `irs-strict-designs-yield-nonsurjunctive-groups` (C2). The dead ends
recorded there are diracization, joins, shape-dependent monotonicity and finitely generated support.
None of them is repeated here.

Nodes written from this artifact:

- `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups` (Section 3, proved);
- `free-group-irs-lie-in-the-atomic-irs-hull` (Section 4, open, with a hardness calibration);
- route `irs-strict-designs-yield-nonsurjunctive-groups-via-atomic-hull` (Section 5).

## 1. Candidate class and mechanism

**Class.** A non-surjunctive group reached as a limit. A strict design `D` on an IRS `mu` of `F_r` is not
tied to any group, but if `mu` is a weak-* limit of finite convex combinations of ergodic atomic IRS, each
atomic component is a coset space `Q_nu x {1..k_nu}` of a finitely generated deck group `Q_nu`
(`atomic-irs-strict-designs-are-nonsurjunctive-quotients`, Theorem 3.1 of
`irs-surjunctivity-heretic-2026-09-17.md`).

**Mechanism a strict automaton needs.** Along the approximation, forward failure `eps_D(nu)` tends to `0`
in mean while reverse failure `delta_D(nu)` stays bounded below. So the components carry designs that are
almost injective, with a small, recorded set of bad layers, yet have a definite density of reverse-bad
layers. Each such component yields an injective automaton over `Q_nu` into a product of many proper
subshift tracks with a slightly larger full track. That is exactly the shape of map that uniform
quantitative surjunctivity (UQS) forbids.

**Where it dies.** The mechanism dies on any group family with a shared UQS constant function. A free
product of all deck groups forces one shared constant by heredity. So on the hull, a strict design
exists only if some countable group is non-surjunctive, or is surjunctive and not UQS.

## 2. Notation

Separate the two variables that the co-sofic referee audit found clashing.

- `Gamma = F_m`, free of rank `m`.
- `d_k` is the size of the radius-`k` ball in the `2m`-regular tree.
- A design `D = (tau, sigma)` has alphabet `A` and radii `R_tau`, `R_sigma`; put `rho = R_tau + R_sigma`.
- Forward-good, reverse-bad, `eps_D`, `delta_D` are as in Section 2 of
  `irs-surjunctivity-heretic-2026-09-17.md`, with `rho` in place of that artifact's second `r`.
- Every radius-`k` ball of every Schreier graph of `Gamma` has at most `d_k` vertices.
- Both events are clopen in `Sub(Gamma)`, so `eps_D` and `delta_D` are continuous affine functionals on
  `IRS(Gamma)`.

UQS is the definition in `amenable-extensions-of-uqs-groups-are-surjunctive`, with constant function
`delta_N(B, w)`. Heredity (Proposition 3.1 of `amenable-extension-surjunctivity-transfer-2026-09-12.md`)
passes UQS to subgroups with the same constant function.

**The atomic hull.** `Hull(Gamma)` is the weak-* closed convex hull in `IRS(Gamma)` of the ergodic IRS
that have an atom. It contains every Dirac mass at a normal subgroup, every IRS supported on finite-index
subgroups, and hence every co-sofic IRS.

## 3. The transfer theorem

**Proposition 3.1 (layered deficit).** Let `nu` be an ergodic atomic IRS of `Gamma` with atom `H`,
`k = [Gamma : N_Gamma(H)]` and deck group `Q = N_Gamma(H)/H`. Let `D` be a design, and suppose `Q` is UQS
with constant function `delta_Q`. Then

```text
delta_D(nu) <= C eps_D(nu),     C = d_(R_tau) + d_(2 rho) ln|A| / delta_Q(A^(d_rho), d_rho).
```

The constant depends only on `D`, `m` and the constant function, not on `nu`.

*Proof.*

**Step 1 (layers).** By the proof of Theorem 3.1 of `irs-surjunctivity-heretic-2026-09-17.md`, the
Schreier graph `X = H\Gamma` is identified with `Q x {1..k}`, and `Q` acts freely on the left by
label-preserving automorphisms, `q'.(q, i) = (q' q, i)`. The layer map `X -> X_0 = N_Gamma(H)\Gamma` is
a morphism of labelled graphs, and `X_0` is a Schreier graph with `k` vertices.

- Balls `B_k((q, i))` and `B_k((1, i))` are isomorphic through the automorphism `q`. So forward-goodness
  and reverse-badness depend only on the layer `i`. Let `E` be the set of forward-bad layers and `R` the set
  of reverse-bad layers.
- `nu` is uniform on the `k` conjugates `g_i^-1 H g_i`, which correspond to the cosets `N_Gamma(H) g_i`.
  The rooted graph of the conjugate `g_i^-1 H g_i` is `(X, H g_i)`, whose root lies in layer `i`. Hence
  `eps_D(nu) = |E|/k` and `delta_D(nu) = |R|/k`.

**Step 2 (the injective automaton).** Define `T : (A^k)^Q -> (A^k)^Q x (A^E)^Q` by
`T(x) = (tau x, x|_(Q x E))`.

- `T` is continuous and commutes with the `Q`-action, since `tau` commutes with label-preserving
  automorphisms. By Curtis-Hedlund-Lyndon it is a cellular automaton over `Q`.
- `T` is injective. If `(q, i)` is forward-good, then `x(q, i) = sigma(tau x)(q, i)`, so `tau x`
  determines `x` on the good layers. The bad layers are recorded in the second coordinate.

**Step 3 (clean reverse-bad layers).** Call a layer `i in R` clean if every vertex of `B_(R_tau)((1, i))`
is forward-good. By Step 1 its image in `X_0` lies in `B_(R_tau)(i)`, so the clean condition only fails
when `B_(R_tau)(i)` meets `E` in `X_0`. At most `|E| d_(R_tau)` layers lie within distance `R_tau` of `E`,
hence

```text
|clean| >= |R| - d_(R_tau) |E|.
```

For a clean `i` with witness `p_i` on `B_rho((1, i))`, and `y = tau x`: `sigma y = x` on
`B_(R_tau)((1, i))`, so `tau(sigma y)(1, i) = tau x(1, i) = y(1, i)`, while `tau(sigma p_i)(1, i) != p_i(1, i)`.
Therefore `y|_(B_rho((1, i))) != p_i`. Translating by `q in Q`, `y` also avoids `q.p_i` on `B_rho((q, i))`.

**Step 4 (separated tracks).** Choose greedily a set `S` of clean layers with pairwise `X_0`-distance
greater than `2 rho`. Each choice removes at most `d_(2 rho)` candidates, so
`n = |S| >= |clean| / d_(2 rho)`, and `n >= 1` whenever `|clean| >= 1`. For `i in S` put
`L_i = B_rho(i)`, a set of at most `d_rho` layers in `X_0`. The sets `L_i` are pairwise disjoint.

- `B_rho((1, i))` lies over `L_i`. Its set of `Q`-coordinates `W_i` has at most `d_rho` elements.
- Let `Y_i` be the set of `z in (A^(L_i))^Q` such that no translate of the partial pattern `p_i` occurs.
  This is a closed `Q`-invariant subset. It misses every full completion of `p_i` on `W_i`, so it misses a
  pattern on at most `d_rho` sites. By Step 3, `(tau x)|_(Q x L_i)` lies in `Y_i`.

**Step 5 (bookkeeping).** If `|clean| = 0`, then `|R| <= d_(R_tau) |E|` and the bound holds. Otherwise
`n >= 1`. Pad the tracks to one alphabet with fresh coordinates that the map copies unchanged:
`T'(x, u) = (T(x), u)` with `u in (A^M)^Q` and `M = n d_rho`. `T'` is an injective automaton over `Q`.

- Assign `d_rho - |L_i|` of the fresh coordinates to track `i`, disjointly across tracks, and put
  `B = A^(d_rho)`.
- **Source.** The track coordinates are `L_i` plus their padding, and the remaining `j = k + M - n d_rho`
  coordinates are full. So the source is `(B^n x A^j)^Q`.
- **Target.** Track `i` lies in `Y'_i = Y_i x A^(pad_i)`, a subshift of `B^Q` missing a pattern on at most
  `d_rho` sites. The full track has `j' = j + |E|` coordinates: the remaining layers of `tau x`, the unused
  padding, and `x|_(Q x E)`.

`j' - j = |E| = eps_D(nu) k`. UQS of `Q`, with `D = A`, `w = d_rho`, forbids `T'` unless

```text
eps_D(nu) k ln|A| >= delta_Q(A^(d_rho), d_rho) n >= delta_Q(A^(d_rho), d_rho) (delta_D(nu) - d_(R_tau) eps_D(nu)) k / d_(2 rho).
```

Dividing by `k` gives the stated bound. QED

**Theorem 3.2 (hull transfer).** Let `mu in Hull(F_m)` carry a strict design `D`. Then some countable
group is not surjunctive, or some countable surjunctive group is not UQS.

*Proof.*

1. **Approximation.** There are finite convex combinations `mu_t = sum_s c_(t,s) nu_(t,s)` of ergodic
   atomic IRS with `mu_t -> mu` weak-*. By continuity, `eps_D(mu_t) -> eps_D(mu) = 0` and
   `delta_D(mu_t) -> delta_D(mu) > 0`.
2. **One group.** Only countably many `nu_(t,s)` occur. Each deck group `Q_(t,s)` is finitely generated,
   since its normalizer has finite index in `F_m`. Let `G` be their free product. It is countable and
   contains every `Q_(t,s)`.
3. **Dichotomy.** If `G` is not surjunctive we are done. If `G` is surjunctive and not UQS we are done.
   Otherwise `G` is UQS with a constant function `delta_G`. By heredity every `Q_(t,s)` is UQS with the
   same `delta_G`.
4. **One constant.** Proposition 3.1 gives `delta_D(nu_(t,s)) <= C eps_D(nu_(t,s))`, with
   `C = d_(R_tau) + d_(2 rho) ln|A| / delta_G(A^(d_rho), d_rho)` independent of `t` and `s`.
5. **Contradiction.** Both functionals are affine, so `delta_D(mu_t) <= C eps_D(mu_t) -> 0`. That
   contradicts `delta_D(mu_t) -> delta_D(mu) > 0`. QED

**Remark 3.3 (why the free product).** Proposition 3.1 is useless with component-dependent constants.
If `delta_(Q_(t,s))` tends to `0`, the bound gives nothing in the limit. That is the same uniformity
failure recorded for directed unions in Proposition 3.1(2) of the UQS artifact. The free product turns
"each deck group is UQS" into "one group is UQS", which is a single instance of
`surjunctive-groups-are-uniformly-quantitatively-surjunctive`.

**Remark 3.4 (the finite case, not used).** Every finite group `Q` is UQS with
`delta(B, w) = |B|^(-w) / w^2`.

- For a window `W` with `|W| <= w`, a maximal family of disjoint translates has at least
  `|Q| / |W W^-1| >= |Q| / w^2` members.
- So a subshift missing a pattern on `W` has at most `|B|^|Q| exp(-|Q| |B|^(-w) / w^2)` points.
- Counting points on both sides of an injective map gives `(j' - j) ln|D| >= n |B|^(-w) / w^2`.

Deck groups of IRS on finite-index subgroups are finite. So Theorem 3.2's argument, run with this constant
instead of the free product, gives `delta_D <= C eps_D` on the closed convex hull of finite-index atomic
IRS. That is the co-sofic set, so it recovers the qualitative content of `co-sofic-irs-carry-no-strict-design`
by a different count, with `d_k` taken in the `2m`-regular tree throughout. This remark is not recorded as
a route, and nothing depends on it.

## 4. The hull prerequisite and its hardness

**Open claim `free-group-irs-lie-in-the-atomic-irs-hull`.** For every `m >= 1`, `Hull(F_m) = IRS(F_m)`.
Every IRS of a free group is a weak-* limit of finite convex combinations of ergodic IRS with an atom.

**Hardness calibration (a conditional remark, not a node).** Assume `m >= 2`. The claim implies that a
non-hyperlinear group exists:

- The character `chi_mu(g) = mu(g in H)` is a continuous affine function of `mu`, because the events are
  clopen.
- Amenable (Connes-embeddable) traces on `C*(F_m)` form a weak-* closed convex set. This is imported as a
  standard fact (Brown-Ozawa, Chapter 6) and is not re-derived here.
- `non-cohyperlinear-irs-exists` gives an ergodic IRS with a non-amenable character. If it lay in the
  hull, some ergodic atomic IRS would have a non-amenable character.
- `atomic-noncohyperlinear-irs-forces-nonhyperlinear` then gives a non-hyperlinear group.

So the hull claim is at least as hard as producing a non-hyperlinear group. The converse fails: a
non-hyperlinear group does not obviously place every IRS in the hull.

**How it can fail on its own.** A nonatomic ergodic IRS whose root statistics are not approximable by
mixtures of layered group coset spaces would refute it, whatever the answer on surjunctivity. The
Bowen-Chapman-Lubotzky-Vidick and Manzoor witnesses are non-co-sofic, but it is not known whether they lie
in the hull. They are the first test cases.

## 5. Decompositions

```text
C2 = irs-strict-designs-yield-nonsurjunctive-groups
   <=  HULL : free-group-irs-lie-in-the-atomic-irs-hull
     + UQS  : surjunctive-groups-are-uniformly-quantitatively-surjunctive
     + Theorem 3.2 (proved)
```

*Modus ponens.* Take an IRS carrying a strict design. HULL puts it in the hull. Theorem 3.2 gives a
countable group that is non-surjunctive, or surjunctive and not UQS. UQS excludes the second case.

**Each prerequisite can fail on its own.**

- UQS is a statement about groups. HULL is a statement about the convex geometry of `IRS(F_m)`.
- HULL can fail while every surjunctive group is UQS, if some nonatomic IRS is far from mixtures of atomic
  ones.
- UQS can fail on a nonsofic surjunctive group while HULL holds.

**What this changes.**

1. **The Wave 4 dead ends are bypassed, not repaired.** Diracization and joins try to turn one IRS into one
   group and move a defining condition the wrong way. Theorem 3.2 never builds a group from `mu`. It uses
   the groups already present in approximating atoms and pays for the error with a uniform deficit. The
   forward error `eps` is recorded as a full track rather than repaired.
2. **The deficit is a named invariant for the counterexample side.** On any family of atomic IRS whose deck
   groups share one UQS constant function, `delta_D <= C eps_D` holds with the constant of Proposition 3.1.
   The inequality defines a closed convex set, so it passes to the hull. A C1 witness in the hull must
   therefore break uniformity of the UQS constant along its approximating deck groups. That is the step
   where every hull witness dies unless some group is non-surjunctive or non-UQS.
3. **Where C2 still dies.** Outside the hull there are no approximating atoms and so no deck groups. A
   witness there, a nonatomic IRS carrying a strict design and not approximable by atomic mixtures, is the
   only remaining way C2 can fail while UQS holds. Section 4 shows that ruling such IRS out wholesale needs
   a non-hyperlinear group.
4. **The counterexample root, restricted to the hull.** `some-group-is-not-surjunctive` follows from UQS,
   Theorem 3.2 and a hull IRS carrying a strict design. Every atomic witness is a hull witness, so under UQS
   the root is equivalent to "some hull IRS carries a strict design". This equivalence is not recorded as a
   separate node, since its hull hypothesis is just the root restated with limits allowed.
