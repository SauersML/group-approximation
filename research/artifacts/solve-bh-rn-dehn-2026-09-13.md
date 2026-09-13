# Dehn upper bounds for V_d and V_d(G): what is known, and where the Stein–Farley argument stops (2026-09-13)

Lane `solve-bh-rn-dehn`. Targets: `higman-thompson-vd-has-polynomial-dehn-function`
(at `d = 10`) and `rover-nekrashevych-dehn-polynomial-in-host-and-vd`, which together
would settle `bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function` through
`bs12-poly-dehn-simple-host-via-rn-upper-bound`. Verdict: neither statement is settled.
No node changes status; only Attempts are added.

## 1. Sources pinned

- **Migliorini, arXiv:2410.23088** (abstract, from the arXiv abstract page):
  "We prove that Thompson's group $T$ and, more generally, all the Higman-Thompson
  groups $T_n$ have quadratic Dehn function."
- **Lorrain, arXiv:2608.03813** (abstract): "... Guba showed that Thompson's group $T$
  and $V$ have Dehn functions bounded above by $n^7$ and $n^{11}$, respectively.
  Recently, Migliorini showed that the Dehn function of Thompson's group $T$ is also
  quadratic ... In this paper, we improve the upper bound of the Dehn function of
  Thompson's group $V$ to $n^6$ ..." Only `d = 2`.
- **Zaremsky, arXiv:2305.15176** (`main.tex`, read on MSI):
  - l.114: "Presumably, close relatives like the Higman--Thompson groups $T_d$ and $V_d$,
    which are virtually simple, also have polynomial Dehn functions, using similar
    arguments."
  - l.128: "we suspect that the Dehn function of any $V_d(G)$ should be bounded above by
    some combination of the Dehn functions of $V_d(\{1\})$ and $G$, and this could
    perhaps be approached by looking at the action of $V_d(G)$ on a simply connected,
    cocompact truncation of the Stein--Farley complex of $V_d(G)$ ..."
  - l.227: "If $G$ is finitely generated, then so is $V_d(G)$, and if $G$ is finitely
    presented, then so is $V_d(G)$ (more generally if $G$ is of type $\F_n$ then so is
    $V_d(G)$ \cite[Theorem~4.15]{skipper19})."
- **Literature search.** arXiv listing searches for "Dehn function Higman-Thompson" and
  for `"Dehn function" "Thompson" V_n` returned arXiv:2410.23088, arXiv:2608.03813 and
  arXiv:1402.5652 ("Compact presentability of tree almost automorphism groups", not a
  Dehn-function result). The arXiv API query returned nothing (rate limit). So no source
  found covers `δ_(V_d)` for `d >= 3`. The search is not exhaustive.

## 2. Why the known results do not transfer

- `T_d <= V_d`, but Dehn functions pass neither to subgroups nor to overgroups, so
  Migliorini's theorem says nothing about `V_d`.
- Migliorini's T proof uses normal forms with boundedly many non-F letters. For `V`,
  `thompson-v-elements-need-unboundedly-many-non-f-letters` kills that shape through the
  order-break count. The same count on `d`-ary cones (reversing the `d^k` cones of depth
  `k`) should give the analogous statement for `V_d`; this is a hand remark, not checked.
- Lorrain's `n^6` argument runs on the specific finite presentation of V on
  `x_0, x_1, c_1, π_0` and on Guba's normal form `p π c_(n+1)^m q^(-1)`. Adapting it to
  `V_d` means redoing a 70-page van Kampen count on a different presentation; not
  attempted here.

## 3. The Stein–Farley push-down, analysed (Zaremsky l.128)

Setting: `V_d` acts on the Stein–Farley CAT(0) cube complex `X_d` (vertices: expansions,
height = number of leaves; an edge splits one leaf into `d`), with finite cell stabilizers.
For `k` large the height truncation `X_(<=k)` is cocompact and simply connected, so
`δ_(V_d)` is equivalent to the combinatorial Dehn function of `X_(<=k)`.

- **Filling in `X_d` is quadratic and dimension-free.** In a minimal disc diagram in a
  CAT(0) cube complex, dual curves are embedded arcs from boundary to boundary and two of
  them cross at most once (standard minimal-diagram facts, Sageev / Wise; not re-read
  here). A loop of length `L` therefore bounds a diagram with at most `L^2/4` squares,
  whatever the dimension of the cubes involved.
- **Heights inside that diagram are linear in `L` (sketch).** Every edge changes height by
  `d − 1`, and a vertex can be joined to the boundary by a path crossing only dual curves
  that separate it from the boundary, at most `L/2` of them. So heights stay below
  `k + (d−1)L/2`.
- **Where polynomiality is lost.** The diagram must be pushed down into `X_(<=k)` through
  descending links, level by level, over `O(L)` height levels. The standard Morse-theoretic
  push-down bounds the area by a product of per-level costs, so it only gives a bound
  exponential in `L`. A polynomial bound needs a quantitative descending-link lemma with
  additive cost: a loop of length `l` in the descending link of a height-`h` vertex fills
  with `poly(l, h)` cells, and the new cells' own push-downs must not multiply. No such
  estimate is known to this graph. That is the precise missing input for
  `higman-thompson-vd-has-polynomial-dehn-function`.

## 4. The Röver–Nekrashevych upper bound

- Finite presentation of `V_d(G)` comes from Brown's criterion on the Stein–Farley complex
  (Zaremsky l.227, citing Skipper–Witzel–Zaremsky Theorem 4.15), not from an explicit
  finite presentation. No explicit finite presentation of `V_10(Gamma_2)` was found, so no
  direct van Kampen count is available.
- The push-down route of §3 applies to `V_d(G)`, with cell stabilizers built from copies of
  `G` over the leaves, extended by finite groups. Beyond the §3 gap it needs:
  (a) at most polynomial distortion of the stabilizer copies `ι_w(G)` over cones of depth
  up to `O(L)`; for rational `G`, pushing one root letter of `G` down to the leaves of an
  `O(L)`-leaf tree yields `O(L)` letters of bounded length (finitely many states), which
  suggests linear distortion, but this is not written as a proof;
  (b) additivity of the stabilizer fillings `Σ δ_G(l_i)` across the diagram, which holds
  once (a) bounds the total leaf-word length polynomially and `δ_G` is superadditive.
- So `rover-nekrashevych-dehn-polynomial-in-host-and-vd` reduces, at best, to the same
  additive push-down lemma plus (a). Neither is proved here.

## 5. Consequences for the BS(1,2) route

- The route needs `d >= 3`: affine self-similar realizations of hosts containing BS(1,2)
  act on `Z_p`-digits with `p` odd (2 must be a unit), so the tree has `p^m` children
  (`9`, and `10` after persistence), never `2^m`. The one `V_d` with a polynomial bound on
  main (`d = 2`) is therefore not the one this route needs.
- Honest status: `bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function` stays
  OPEN, reduced to one additive descending-link push-down lemma for `X_d` (`d = 10`) and
  the distortion estimate (a).
