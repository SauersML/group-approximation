# Small-cancellation quotients of hyperbolic Kazhdan groups as stability hosts (2026-09-13)

Lane `solve-sc-hyperbolic-kazhdan`. Target: `non-hyperlinear-group`, via one flexibly
HS-stable hyperbolic Kazhdan group with `b_2 >= 1`
(`kazhdan-hyperbolic-b2-group-flexibly-hs-stable`), obtained by attaching
small-cancellation relators to a base such as the GHB_2(7) congruence kernel.

**Verdict: route refuted as a cohomological mechanism; no stability mechanism found.**
One elementary obstruction claim landed:
`relator-adjunctions-grow-degree-two-cohomology`.

## 1. What the kills node consumes

`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` (route
`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof`) needs exactly:

- `Γ` word-hyperbolic;
- property (T), used only for (T;FD) and finite `H_1`;
- `b_2(Γ;Q) >= 1`, used to build an integral central extension with finite abelianization;
- flexible HS stability, in Dogon–Vigdorovich's Definition 1.2.

It then imports Dogon–Vigdorovich Theorem 1.3 (`hs-stability-forces-nonhyperlinear-central-extension`)
and uses quasi-isometry invariance of hyperbolicity. A small-cancellation quotient `Q`
of a hyperbolic Kazhdan group stays Kazhdan (quotient), and stays hyperbolic under
small cancellation over a hyperbolic group (Olshanskii-type theorems; not re-read here).
So the only hypotheses in question are `b_2(Q) >= 1` and stability.

## 2. Kill tests

**(a) `b_2` is preserved, and grows.** If the relator complex `Y = X ∪_R e²` is
aspherical, then `b_2(Q) = b_2(Γ) + |R|` and `b_2^(2)(Q) = b_2(Γ) + 1 + |R|`
(landed claim, items 1–2). So adding relators can never break the `b_2 >= 1` clause.
Asphericity of relative small-cancellation presentations over hyperbolic groups is the
open input. I found no source this session: the arXiv API returned nothing from MSI,
and the web search budget was exhausted. The claim keeps asphericity as a hypothesis.

**(b) Relators make the degree-two obstruction worse.** The only stability-existence
scheme on main is the degree-two Newton iteration
(`hs-stability-from-bounded-degree-two-primitives`, De Chiffre–Glebsky–Lubotzky–Thom).
It needs `H²(Q; Ad) = 0` with a modulus. The landed claim (item 3) shows `H²(Q;Ad) ≠ 0`
on the trivial summand, and on a traceless regular summand whenever `Q` is hyperlinear.
Both grow by `|R|`. So relators cannot be the source of degree-two vanishing. This
generalizes `ghb7-kernel-blocks-degree-two-newton-stability` from `H` to every
aspherical relator quotient.

**(c) Non-circularity.** Combining two established nodes:

- `hyperlinear-flexibly-hs-stable-group-is-residually-finite`: a stable hyperlinear `Q`
  is residually finite;
- `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`: a stable hyperlinear
  hyperbolic Kazhdan `Q` with `b_2 >= 1` carries a persistent prime degree-two class, so
  it is not good.

So every relator choice falls into one of two known hard targets:

- relators that kill finite quotients (the Kozma–Lubotzky effect: destroying
  low-dimensional representations) make `Q` non-residually-finite, and then stability
  of `Q` is non-hyperlinearity of `Q` itself;
- relators that keep `Q` residually finite force Gromov-question strength
  (a persistent class).

A stability proof is not logically circular: it doesn't assume hyperlinearity. But it
is no easier than those targets. Becker–Lubotzky
(`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`) leaves only the flexible notion
in the hyperlinear case.

**(d) The class-wide screen.** By `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`,
an argument covering a class closed under Belegradek–Osin covers settles
`non-hyperlinear-group` outright. Belegradek–Osin covers are built by relative small
cancellation over hyperbolic groups (construction not re-read in this lane). So an
argument that works for "all small-cancellation quotients of hyperbolic Kazhdan groups"
is screened, and a mechanism must use the specific relator words.

**(e) Kazhdan-kernel transfer doesn't apply.** Stability descends to quotients by
Kazhdan normal subgroups (`flexible-hs-stability-passes-to-kazhdan-kernel-quotients`). But
no flexibly stable infinite Kazhdan base is known, and normal closures of
small-cancellation relators need not have (T). There is no transfer in either direction.

**(f) "Almost-invariant vectors of bounded codimension."** In a Kazhdan group,
almost-invariant vectors are already near invariant vectors, and relators don't create
new ones. Stability is an existence statement for nearby genuine representations, which
is the degree-two question of (b). No relator mechanism for existence was found.

## 3. Exact remaining gap

A non-cohomological stability mechanism, specific to chosen relator words, for one
hyperbolic Kazhdan quotient with `b_2 >= 1`. By (c) it would either prove that quotient
non-hyperlinear directly, or produce a residually finite, not-good hyperbolic group. No
candidate mechanism is known. Asphericity of relative small-cancellation presentations
over hyperbolic groups is a side input only; it controls `b_2`, which (a) already shows
is not the bottleneck.
