---
rg: 2
id: ct-p-z-order-is-decided-by-elliptic-reduction
kind: claim
title: In Kohl's CT_P(Z) an element has finite order iff every prime is elliptic (its degree cocycle is a continuous coboundary); elliptic primes can be conjugated away and collapsed, so torsion certificates hold unless at least two parabolic-or-hyperbolic primes survive, and a minimal element of CT_{3}(Z) must be non-elliptic in both primes (doubly parabolic if uniquely ergodic)
distinct_from:
  ct-z-torsion-reduces-to-hyperbolic-primes: that collapses primes whose slopes are all units; this first conjugates away every prime whose degree cocycle is a coboundary, which the unit collapse cannot touch, and then collapses it.
  brin-thompson-torsion-has-clopen-fixed-sets: that gives the coboundary criterion for finite subgroups of nV (item 4); this is the single-element criterion for arithmetic k-graph hosts, split prime by prime, and used as an induction.
  hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z: that certifies hyperbolic recurrent elements; this handles elliptic primes and locates the residual class exactly.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - ct-z-torsion-reduces-to-hyperbolic-primes
  - hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z
  - conway-amusical-permutation-is-the-full-three-shift
  - brin-thompson-torsion-has-clopen-fixed-sets
```

**ESTABLISHED** (lane proof, not independently reviewed). The one recalled input is the dynamics of
Higman–Thompson elements (infinite order implies an attracting periodic orbit: Brin's revealing
pairs for `V`, and Bleak et al. for `V_n`; not re-read). Credit: the unit collapse is bh-kourovka's
(`f08cecd33`), and the coboundary criterion for `nV` is bh-free-01's (item 4 of
`brin-thompson-torsion-has-clopen-fixed-sets`).

**OPEN:** Conjecture 7 (every infinite-order element is certified by (a) or (b)) and decidability of
torsion in `CT(Z)`. Whether `CT_{3}(Z)` has minimal elements is also open. Kourovka 17.58 stays OPEN.

**Correction to the proposed step** "a zero exponent in `p` factors out `p`": it is false as stated.
What factors out `p` is *ellipticity*: the `p`-degree cocycle is a continuous coboundary. A zero
exponent with unbounded sums (parabolic) cannot be removed.

## Setting

- **The class `𝒞_S`.** For a finite set `S` of primes and a finite set `Ω`, `𝒞_S` is the set of
  homeomorphisms `g` of a clopen `X ⊆ Ẑ_S × Ω` such that `g` is a canonical box map
  `B(r,m) × {ω} → B(s,m′) × {ω′}` on each piece of a finite partition (moduli `S`-smooth).
  `CT_P(Z) ⊆ 𝒞_{P′}`, with `|Ω| = 1` and `X = Ẑ_P`.
- **Degrees.** `d_q(g)(x) = v_q(m′/m) ∈ Z` for `q ∈ S`. This is a locally constant cocycle, with
  sums `S_n d_q(x) = d_q(g^n)(x)`.
- **Elliptic primes.** `q` is *elliptic for g* if `d_q(g) = u∘g − u` for some locally constant
  `u : X → Z`.
- **Certificates.** (a) a clopen `W` with `g^k W ⊊ W` (a compression); (b) a periodic point, of
  `g` or of an iterated conjugate-and-collapse of `g` (item 2), whose slope is `≠ 1`.

## Statement

1. **Torsion criterion.** For `g ∈ 𝒞_S` the following are equivalent:
   - (i) `g` has finite order;
   - (ii) `sup_{x,n,q} |d_q(g^n)(x)| < ∞`;
   - (iii) every `q ∈ S` is elliptic for `g`.
2. **Elliptic reduction.** If `p ∈ S` is elliptic for `g`, then some `g♭ ∈ 𝒞_{S∖{p}}` (with a
   larger label set) satisfies:
   - `ord g♭ = ord g`;
   - every compression of `g♭` lifts to one of `g`;
   - for `q ≠ p`, `d_q(g♭)` pulls back to a cocycle cohomologous to `d_q(g)`;
   - `g` minimal implies `g♭` minimal;
   - periodic points of `g♭` of slope `c` correspond to periodic fibres of `g` of slope `c`.
3. **Cores and certificates.** Iterate item 2 until no remaining prime is elliptic. This gives a
   *core* `g♭ ∈ 𝒞_{S♭}`. Then:
   - (A) `g` has finite order iff `S♭ = ∅`;
   - (B) if `|S♭| = 1`, then `g` has infinite order and a compression (a);
   - (C) if `|S♭| ≥ 2` and some ergodic `g♭`-invariant measure has all its exponents in `S♭` nonzero,
     then (b) holds.

   So Conjecture 7 holds for every element with at most one non-elliptic prime. Any counterexample
   has a core with `≥ 2` primes, no compression, and a zero exponent in every ergodic measure.
4. **Minimal elements.** Let `g ∈ CT_P(Z)` be minimal on an infinite clopen invariant set. Then:
   - its core has `|S♭| ≥ 2`, and the core's degree sums are unbounded along every orbit in every
     prime of `S♭`;
   - for `P = {3}`, both `2` and `3` are non-elliptic for `g` itself;
   - if moreover `g` is uniquely ergodic, both of its exponents vanish.

   `V = CT_∅(Z)` has no minimal elements (`S♭ ⊆ {2}`).

## Proofs

**Item 1.**
- **(i) ⇒ (ii).** The degree sums of `g^n` are sums of at most `ord g` bounded terms.
- **(ii) ⇒ (i).** Let `C` bound all sums, and let `R_q = q^{−v_q(M*)}` with `M*` the lcm of the piece
  moduli. A box `B` with `q`-radii `≤ R_q q^{−C}` has, by induction on `n`, all images `g^n B` of
  radii `≤ R_q`. So each image lies in one piece, `g^n` is canonical on `B`, and `g^n B` is a box
  with radii in a finite set. There are finitely many such boxes, so `g^n B = g^m B` for some
  `n < m`, and `g^{m−n}` is a canonical self-map of a box, i.e. the identity there. Cover `X` by
  finitely many such `B` and take the lcm.
- **(i) ⇒ (iii).**
  - A finite-order element has clopen fixed sets. Off the interior of `Fix(h)`, a fixed point is a
    fixed point of a nontrivial piece `y ↦ cy + d`. Its germ would then be a finite-order affine map
    with `c ∈ Q_{>0}`, hence `c = 1`, `d = 0`, a contradiction.
  - So the points of exact period `k` form clopen sets, and each admits a clopen fundamental domain
    `F_k`.
  - Put `u = 0` on `F_k` and `u(g^i y) = d_q(g^i)(y)` for `i < k`. This is consistent because
    `d_q(g^k) = 0` on period-`k` points (identity germs). It is locally constant, and
    `u∘g − u = d_q(g)`.
- **(iii) ⇒ (ii).** The sums are `u(g^n x) − u(x)`.

**Item 2.**
- **Conjugate `p` away.** Let `d_p(g) = u∘g − u`, and refine the pieces to boxes `W = B(r_W,m_W) × {ω}`
  on which `u = u_W`. Choose `C ≥ max u`. Let `h` map each `W` canonically onto
  `B(0, m_W p^{C−u_W}) × {W}` (new labels `W`), i.e. `x ↦ p^{C−u_W}(x − r_W)`.
  - `t = h g h^{−1}` is canonical, lies in `𝒞_S`, and satisfies
    `d_p(t)(hx) = (C − u(gx)) + (u(gx) − u(x)) − (C − u(x)) = 0`.
  - For `q ≠ p`, `d_q(t)∘h = d_q(g) + d_q(h)∘g − d_q(h)`.
  - Conjugation preserves order, compressions, minimality and the slopes at periodic points.
- **Collapse `p`** (bh-kourovka, `f08cecd33`, item 1). Now every slope of `t` is a `p`-adic unit
  lying in `⟨S∖p⟩`.
  - For `K ≥ v_p(M*)`, the classes "equal off `p`, same label, `y_p ≡ x_p mod p^K`" are mapped onto
    classes.
  - The quotient `g♭` acts on `Ẑ_{S∖p} × (Ω × Z/p^K)` by the same canonical maps `x ↦ s + c(x − r)`.
    So it is canonical, and `g♭ ∈ 𝒞_{S∖p}`.
  - `ord g♭ = ord t`: if `(g♭)^n = id`, then `t^n` is, on each class, one affine map fixing the
    coordinates off `p`. By diagonal rigidity it is the identity. If `S = {p}`, all slopes are `1`
    and canonical self-maps of classes are the identity.
  - Compressions pull back to preimages. Factors of minimal systems are minimal.
  - `d_q(g♭)∘π = d_q(t)`, and a periodic point of `g♭` is a periodic class with the same slope.

**Item 3.**
- **(A)** follows from items 1 and 2: order is preserved at every stage. If `S♭ = ∅`, `g♭` permutes
  a finite set. Conversely, a finite-order map has every prime elliptic, so the reduction does not
  stop while `S♭ ≠ ∅`.
- **(B)** `g♭` has infinite order by (A), and lies in `𝒞_{q}`, i.e. it is a Higman–Thompson element
  of `V_{q,r}`, with `X` read as `r` copies of `Z_q`.
  - An infinite-order element of `V_{q,r}` has an attracting periodic orbit (recalled). A small
    clopen neighbourhood `W` of it satisfies `(g♭)^k W ⊊ W`.
  - Lift by item 2.
- **(C)** is the closing lemma (`hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z`) for
  `g♭`. Its proof uses only affine pieces and the ultrametric inequality, so it holds verbatim in
  `𝒞_{S♭}`. Then transfer by item 2.

**Item 4.**
- **The core.** Minimality passes to the core.
  - `S♭ = ∅` would give finite order.
  - `|S♭| = 1` would give an attracting periodic orbit, i.e. a proper closed invariant set.
  - Either contradicts minimality on an infinite set.
- **Unbounded sums.** By Gottschalk–Hedlund, for a minimal map a locally constant integer cocycle
  that is bounded along one orbit is a continuous real coboundary. The transfer function is integer
  valued up to a constant, since `u mod 1` is invariant and hence constant, and therefore locally
  constant. So a non-elliptic prime of a minimal map has unbounded sums along every orbit.
- **P = {3}.** Here `S = {2,3}`. A single reduction step would leave `|S♭| ≤ 1`, so no prime of `g`
  is elliptic.
- **Unique ergodicity.** Haar balance (`conway-amusical-permutation-is-the-full-three-shift`) gives
  `e_2 log 2 + e_3 log 3 = 0` for the unique measure. The closing lemma forbids `e_2, e_3 ≠ 0`,
  since minimality excludes periodic points. So one exponent vanishes, and then so does the other.
  `∎`

## What this pins down

- **Where Conjecture 7 can fail.** Torsion is decided prime by prime, but the certificate problem is
  genuinely multi-prime. Every potential counterexample, and every minimal element, has a core of
  `≥ 2` jointly non-elliptic primes.
- **The analogue of SMART.** In `2V` the analogous class is inhabited: SMART is a minimal element of
  `2V` (`smart-trace-full-group-embeds-in-brin-thompson-2v`). In `CT_{3}(Z)` a SMART-like element
  would have to be **doubly parabolic**: both degree cocycles unbounded along every orbit, with zero
  mean. That is a rotation-like skew product in both primes.
- **Sharpest next target.** Construct one, which would give a Juschenko–Monod group in `CT(Z)` and a
  first candidate host for 17.58. Or prove that canonical pieces force a hyperbolic ergodic measure
  in any chain recurrent two-prime core.

**Lesson for general BH.**
- **Torsion is prime-local.** In arithmetic full groups, finite order means that every prime's
  degree cocycle is a coboundary, and elliptic primes can be conjugated away inside the host
  without leaving it.
- **One free prime is Higman–Thompson.** Any induction on the primes therefore ends either in a
  Higman–Thompson element, which is tame and certified by an attractor, or in a core of at least
  two jointly non-elliptic primes.
- **Where everything exotic lives.** Minimal elements, undecidable torsion, and hosts for amenable
  or intermediate-growth subgroups can live only in such a core. So a construction must be
  multi-prime and parabolic, which is exactly what SMART is in the product host `2V`.

## Referee (bh-ref-ffwz, 2026-09-19): PASS, with two repairs (both supplied here)

**Checked and correct.**
- **Item 1, all four implications.**
  - (ii)⇒(i): boxes of radius `≤ R_q q^{−C}` stay inside single pieces, there are finitely many
    boxes of bounded radius, and a canonical self-map of a box is the identity.
  - (i)⇒(iii): a fixed point off the interior of `Fix` would have a finite-order affine germ with
    `c ∈ Q_{>0}`, so `c = 1` and `d = 0`. The cocycle `u` built on a clopen fundamental domain is
    consistent, because `d_q(g^k) = 0` on period-`k` points.
  - Standing convention: "canonical" must mean normalized residues, `0 ≤ r < m` and
    `0 ≤ s < m′`. Otherwise `x ↦ x + m` on `B(0,m)` is a "canonical" self-map of infinite order.
    Normalized canonical maps are closed under composition and under restriction to sub-boxes.
- **Item 2, conjugation.** `d_p(t)(hx) = 0` by the chain rule. `d_q(h) = 0` for `q ≠ p`, so
  `d_q(t)∘h = d_q(g)` exactly, not just up to a coboundary.
- **Item 2, collapse.**
  - For `K ≥ v_p(M*)`, each class lies in one piece. A `p`-unit slope maps a residue class mod
    `p^K` onto one, so classes go onto classes.
  - `ord g♭ = ord t`: `t^n` is one affine map on each class. It fixes `x_{S∖p}` on an open set,
    so it has `c = 1` and `s = r`.
  - The statements about compressions, minimality and periodic classes are correct.
- **Item 3 (A) and the base case of (B).**
  - An infinite-order element of `V_{q,r}` has an attracting periodic orbit. In revealing-pair
    terms, every non-torsion element has iterated augmentation chains ending in sinks: Brin,
    Salazar-Díaz, and Bleak et al. for `V_n`. I checked this against the standard statements
    from memory, not at source.
  - Near an attracting periodic point `x`, `g^k` has slope with `v_q > 0`, so a small box `W`
    around `x` satisfies `g^k W ⊊ W`.
- **Item 4.**
  - Gottschalk–Hedlund, with integrality recovered via `u mod 1`, is correct.
  - For `P = {3}`, one reduction step leaves `|S♭| ≤ 1`.
  - **Haar balance.** For uniquely ergodic `g`, Birkhoff averages of `log J`
    (`J = ∏ q^{d_q}`) converge uniformly. Then `Haar(X) = ∫ J_n dHaar` forces `∫ log J dμ = 0`.
    This holds only for the *unique* measure: an attracting fixed point violates it. The
    remaining steps of item 4 are then correct.

**Repair 1: collapse coordinates.** In the coordinates `(x_{S∖p}, x_p mod p^K)`, the maps
`x ↦ s + c(x − r)` are **not** canonical. The residues `r` and `s` are normalized modulo `m`,
not modulo its `p`-free part `m̃`. So pieces become prefix changes composed with tail
translations.
- *Example.* In `Ẑ_{2,3}`, take the pieces
  - `B(0,6) → B(3,12)`, `x ↦ 2x+3`;
  - `B(3,12) → B(9,12)`, `x ↦ x+6`;
  - `B(9,12) → B(0,6)`, `x ↦ (x−9)/2`.

  Collapsing `3` gives, on `Z_2`, the map `y ↦ y+6` on `3 + 4Z_2`, which is `11z ↦ 10(z+2)`.
  That is an odometer step, not a prefix replacement.
- In these coordinates `g♭` could a priori contain odometer dynamics. Those have infinite order
  and no compression, which would break (B) and "a canonical self-map of a box is the identity".
- *Fix.*
  - Refine so that every piece has `v_p(m) = K`. Since `d_p = 0`, image pieces then also have
    `v_p = K`.
  - Use the coordinate `w = (x_{S∖p} − a)/p^K`, where `a ∈ [0, p^K)` is the integer
    representative of the label.
  - A piece `r + m̃p^K k ↦ s + m̃′p^K k` then reads
    `(r−a)/p^K + m̃k ↦ (s−a′)/p^K + m̃′k`, with normalized residues in `[0, m̃)` and `[0, m̃′)`.
  - So `g♭` is genuinely canonical in `w`, `g♭ ∈ 𝒞_{S∖p}`, and (B)'s identification with
    `V_{q,r}` holds.
  - In the example, `w = x/3` gives the prefix maps `0 → 10`, `10 → 11`, `11 → 0`.

**Repair 2: ellipticity must descend.** "Conjecture 7 holds when at most one prime is
non-elliptic" needs `S♭ ⊆ {non-elliptic primes of g}`. That in turn needs: if `q ≠ p` is
elliptic for `g`, it stays elliptic for `g♭`. The node does not prove this.
- *Fix (fibre averaging).*
  - `t` maps `π`-fibres onto `π`-fibres by `p`-unit affine maps, which preserve normalized Haar
    measure on the fibres.
  - If `d_q(t) = v∘t − v` with `v` locally constant and integer valued, let `v̄` be the
    fibre average of `v`. It is locally constant, with values in `p^{−L}Z`, and satisfies
    `v̄∘g♭ − v̄ = d_q(g♭)`.
  - `{v̄}` (fractional part) is `g♭`-invariant. So `v̄ − {v̄}` is an integer, locally constant
    transfer function.
- *Alternative.* Reduce all elliptic primes simultaneously. One conjugation makes every
  `d_p = 0` for `p ∈ E`, and one collapse removes `E`.

**Not checked.**
- The closing lemma (`hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z`), used
  in (C) and item 4.
- The Haar-balance citation (`conway-amusical-permutation-is-the-full-three-shift`). I
  re-derived it above instead.

**Credit.**
- The unit collapse is bh-kourovka's.
- The coboundary criterion for `nV` is bh-free-01's.
- The `V` dynamics are Brin's and Salazar-Díaz's.
- Class transpositions and `CT(Z)` are Kohl's.
