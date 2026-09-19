---
rg: 2
id: ct-p-z-order-is-decided-by-elliptic-reduction
kind: claim
title: In Kohl's CT_P(Z) an element has finite order iff every prime is elliptic (its degree cocycle is a continuous coboundary); elliptic primes can be conjugated away and collapsed, so torsion certificates hold unless at least two parabolic-or-hyperbolic primes survive, and a minimal element of CT_{3}(Z) must be non-elliptic in both primes (doubly parabolic if uniquely ergodic)
requires:
  - ct-z-torsion-reduces-to-hyperbolic-primes
  - hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z
  - conway-amusical-permutation-is-the-full-three-shift
  - brin-thompson-torsion-has-clopen-fixed-sets
distinct_from:
  ct-z-torsion-reduces-to-hyperbolic-primes: that collapses primes whose slopes are all units; this first conjugates away every prime whose degree cocycle is a coboundary, which the unit collapse cannot touch, and then collapses it.
  brin-thompson-torsion-has-clopen-fixed-sets: that gives the coboundary criterion for finite subgroups of nV (item 4); this is the single-element criterion for arithmetic k-graph hosts, split prime by prime, and used as an induction.
  hyperbolic-measures-give-hyperbolic-periodic-points-in-ct-p-z: that certifies hyperbolic recurrent elements; this handles elliptic primes and locates the residual class exactly.
---

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
