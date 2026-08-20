# Fractional branch pressure: audit of the 2026-08-19 dossier

Date: 2026-08-19

## 1. What the dossier proposed, and what the graph already had

The dossier ("make the error spread", sharpened) proposed six things.  A
novelty sweep against `research/` before authoring found that three of them
were already present, one was already repo doctrine, and two were new.

| dossier item | verdict |
| --- | --- |
| Perron/branching pressure with a rational subeigenvector | present: `perron-frobenius-branching-carrier-collapse`, `rational-supercritical-branch-certificate`, `strongly-connected-branching-gives-rational-pressure` |
| approximate branches with Gram penalty | present: `gram-branching-capacity-with-overlap` |
| fractional (partial) source projections and `q_0+q_1>1` | **new** |
| soft block mass thresholded into an exact branch | **new lemma**; its special case is the proved note `TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` |
| "copy bad regions until they collide" | already `gram-branching-capacity-with-overlap` (GBC1) at `P=1`; the marked-copy corollary is new |
| "the incompatibility must be coordinate-dependent, not a universal projection identity" | already doctrine: `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md` sections 6-7, `universal-atlas-ideal-cannot-force-hall-deficit`, `fixed-atlas-transport-cost-cannot-separate` |
| ZPC: bounded-degree context-collision code / PCP | superseded on 2026-08-20 by `odd-selector-priority-decoding`: overlap needs no penalty.  The remaining bounded-degree spanning-tree consistency target is `zpc-context-mismatch-transducer`. |

## 2. The two genuinely new lemmas

**Soft block mass yields an exact fractional branch.**  For projections `P,Q`
and a contraction `W` in a finite tracial von Neumann algebra, put `X=QWP` and
`E_t=1_[t,1](|X|)`.  Then

```text
tau(E_t) >= (||X||_2^2 - t^2 tau(P))/(1-t^2),
tau(E_t) <= ||X||_2^2/t^2,
```

the polar part of `X` restricted to `E_t` is a partial isometry with source
exactly `E_t` and range inside `Q` (leakage exactly zero), and two such
branches obey `||T_e^*T_f||_2 <= t^(-2)||X_e^*X_f||_2`.  Node
`soft-block-mass-yields-fractional-branch`.

Consistency check: on one raw character cut `F` and one transported cut `G`
with `tau(F)=tau(G)=1/8`, `tau(FG)=1/64`, the formula at `t=1/4` gives
`tau(E_t) >= 1/120`, which is exactly `(SFF2)` of
`TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md`.  The general lemma reproduces the
already-proved special case.

**Fractional-source branch pressure.**  Allow every edge's source `E_e` to be a
strict subprojection of its state, `tau(E_e) >= c_e tau(P_i) - a_e`, form the
*rational* matrix `B_(ji)=sum_(e:i->j) c_e`, and the capacity argument still
gives `x >= Bx - eta`.  Node `fractional-source-branch-pressure`.  For the
Pauli two-child cell this replaces "both children return almost completely" by

```text
q_0 + q_1 > 1
```

because the three-state matrix on `{E,R_0,R_1}` has `rho^2=q_0+q_1`.

## 3. The consistency gate, made quantitative

A supercritical network built only from canonical data cannot exist: its
carrier masses, branch matrix and error term all converge to the exact model's,
where a certificate would force `y . x = 0` against `tau(E)=1/8`.  Node
`supercritical-network-needs-noncanonical-cuts`.  This is the general form of
what `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md` section 6 proves for the
Reynolds translations, and of the "falsification gate" bullet already in
`atlas-supercritical-pauli-branching-cycle`.

The concrete instance is sharp and is the main negative number of this audit.
On the raw/comb Fourier-flat character cuts, with `tau(F_eps)=1/8` and
`tau(F_eps G_eta)=1/64` for all sixteen pairs, the guaranteed source fractions
out of one raw cut total

```text
sum_eta c_eta(t) >= 4(1/8-t^2)/(1-t^2),
```

which is at most `1/2` and is positive only for `t^2<1/8`; and the Chebyshev
ceiling is `sum_eta c_eta(t) <= 1/(2t^2)`, hence at most `1` for every
`t >= 1/sqrt(2)`.  **The character-level states are subcritical by a factor of
two at best.**  Supercriticality therefore cannot come from character block
masses; it must come from finer, coordinate-selected cuts, or from a spectral
distribution demonstrably spikier than the mass alone forces.

## 4. Numbers used

- Marked separation `||W-1||_2 >= alpha` and `theta=1/2` give
  `tau(Q) >= 3 alpha^2/(16-alpha^2)`; at `alpha^2=2` this is `3/7`
  (`marked-hs-separation-forces-spectral-density`).
- Three projections of trace `3/7` have total ordered overlap at least
  `(9/7)^2-9/7 = 18/49` (`marked-copy-collision-forces-overlap-mass`).
- A contraction in `M_4(N)` is at distance at least
  `(1/sqrt(2)-1/2)^2 = 3/4-1/sqrt(2)` in squared normalized HS from any
  constant-block operator whose coefficient has `||C||_2=1/sqrt(2)`
  (`constant-block-contraction-gap`).

## 5. External status as of 2026-08-19 (dossier's own claim, recorded, not verified here)

The dossier reports that no paper claiming an explicit non-hyperlinear group
exists: Dogon-Vigdorovich (arXiv 2506.20843) reduce it to a flexible
Hilbert-Schmidt stability question, Taller-Vidick note perfect completeness in
their LCS result would imply one, and a 2026 paper still hypothesises one.
Nonsofic groups do exist; Kun-Thom (arXiv 2608.06222) give further explicit
examples.  The Kun-Thom import is already the established
`kun-thom-nonsofic-wreath`.  These citations were taken from the dossier and
have **not** been independently source-checked in this pass; treat the
Dogon-Vigdorovich and Taller-Vidick lines as unverified until a citation audit
covers them.

## 6. Deliberately not authored

- Any ZPC node.  `zpc-context-mismatch-transducer` and
  `zpc-robust-compiler-from-context-transducer` already carry the dossier's
  section 4 in more detail than the dossier states it.
- A separate "copy until collision" capacity lemma.  It is `GBC1` at `P=1`.
- Any node asserting that spikiness implies non-hyperlinearity.  The
  dichotomy `pauli-block-tail-or-flat-rigidity-dichotomy` is recorded OPEN with
  its real gap named: flatness of the sixteen blocks gives sixteen scaled
  partial isometries, not one *common* coefficient `C`; recovering the common
  block still needs the four coordinate shifts of
  `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md` section 7.
