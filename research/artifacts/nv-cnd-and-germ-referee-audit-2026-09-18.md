# Adversarial audit of two unrefereed nV claims (2026-09-18)

Lane `swarm-0917`, agent `e2-w2-audit-nv1`, role referee, family `calibration`.
Targets, both of which landed **ESTABLISHED** on `main` in the previous wave with no
referee stage:

- `brin-thompson-nv-max-type-size-functions-are-not-cnd` (+ its route `-proof`)
- `nv-point-germ-groups-embed-in-zn-by-slope` (+ its route `-proof`)

Three lenses per claim, as assigned: (1) the first step that does not follow;
(2) every import against its own hypotheses and quantifiers; (3) calibration against
1V (Farley's Haagerup proof), SFT full groups and Nekrashevych groups — does the
argument prove too much?

**Verdicts: both SURVIVE.** No step was refuted. Three inaccuracies of statement (all
harmless, listed below), one redundant hypothesis that can be dropped for a stronger
theorem, and one parameter (`beta >= 1/4`) that the audit improves to `beta >= 1/5`
with a new exact certificate.

New artifacts, all in `experiments/nv-cnd-audit-2026-09-17/`, sharing no code with the
audited lane's `experiments/brin-thompson-cnd-2026-09-17/`:

| file | what it checks |
|---|---|
| `audit_linf_certificate.py` | the zero-sum spectrum of the `l^inf^beta` kernel, an independently derived integer certificate verified in **rational interval arithmetic**, exact re-verification of the lane's stored certificates, and the five-point integer witness |
| `audit_brick_lemma.py` | an independent 2V implementation (no guillotine DP; canonicity by diagram refinement, `L` by exact cover) checking item 1 of the non-cnd claim |
| `audit_calibration_1v.py` | the 1V calibration: leaf count is subadditive, hence linear, hence index 0 |
| `audit_germ_slope.py` | the slope cocycle, the compression of item 4 and the saddle of item 5, computed in 2V |
| `audit_beta_range.py` | how far below `1/4` a finite grid pushes the obstruction |
| `beta_one_fifth_certificate.json`, `beta_three_twentieths_certificate.json` | exact integer certificates at `beta = 1/5` and `beta = 3/20` |

---

## A. `brin-thompson-nv-max-type-size-functions-are-not-cnd`

### A.1 Lens 1 — the first step that does not follow

Every step was re-derived. Three statements are inaccurate as written; none is load
bearing, and each is recorded here so a later reader does not mistake it for a gap.

**(a) Step 0 mis-states the power of a baker map.** The route writes

> For `k >= 0` it is `(w a s, t, z) -> (w s, a t, z)` with `|a| = k`.

The actual power stacks the transferred letters in the reverse order:
`b_1^2 (1 a_1 a_2 s, t) = (1 s, a_2 a_1 t)`, checked directly for `k = 1..4` in
`audit_brick_lemma.check_power_shape`. Both uses survive verbatim:

- Step 1 only counts the `2^k` domain bricks `[w a]`, and the count does not change;
- Step 2 only uses *which input letters the second output depends on*, namely letters
  `2..q+1` of the first coordinate, and reversal does not change that set.

**(b) Step 2's measure bound is about `W = B n P`, not about the diagram brick `B`.**
The route is careful (`u'_1 = the longer of u_1 and "1"`), but the bound is false for
the diagram brick itself, and a reader who drops the prime sees an apparent
counterexample. Concretely, for `w = (0, 0, q)` the brick `[0] x C` is canonical and
meets `[00] x C` at total depth `1`, while `|pref| + |m| = 2`. The route's own
quantity, `depth(B n P)`, was checked over **all** canonical bricks (a superset of the
bricks of any diagram) for all `343` elements with `|m|, |p|, |q| <= 3`:

```
piece [00], |e|=0..3: min depth(B n P) = 2,3,4,5   required >= 2,3,4,5
piece [01], |e|=0..3: min depth(B n P) = 2,3,4,5   required >= 2,3,4,5
piece [1],  |e|=0..3: min depth(B n P) = 1,2,3,4   required >= 1,2,3,4
                                        violations 0, and the bound is tight
```

So `L(g(w)) >= 2^||w||_inf` and `D(g(w)) >= ||w||_inf` hold, by a measure argument
that needs no minimisation algorithm at all. This is the half of item 1 that the
obstruction actually consumes.

**(c) Item 1's upper bound, checked by an independent minimiser.** `L` and `D` were
recomputed by exact cover over the dyadic cells (branch and bound on the first
uncovered cell), with canonicity decided by refining the diagram over the brick — a
different algorithm from the lane's guillotine DP. For all `125` elements with
`|m|, |p|, |q| <= 2`: `2^||w||_inf <= L <= 2^|m| + 2^|p| + 2^|q|` and
`||w||_inf <= D <= ||w||_inf + 2`, **zero violations**. Sample:
`w = (-2,-2,-2): L = 12` (bounds `[4, 12]`), `w = (-2,-1,0): L = 7` (bounds `[4, 7]`).

**Steps 3-7 hold as written.**

- Step 4 (Schoenberg subordination) is proved in place and is correct; the
  contrapositive uses `alpha = 1/(4 beta) in (0, 1]`, which covers `beta = 1/4`
  directly and every `beta > 1/4` through `K_{1/4} = K_beta^{1/(4 beta)}`.
- Step 5's `G -> infinity` argument needs `2^beta - eps > 1`, i.e. `beta > 0`; fine.
- Step 5.3 needs `G(lambda d) != 0` for large `lambda`, which 5.1 supplies.
- Step 7 reproduces exactly: the five `l^inf` distances give
  `sum c_i c_j ||x_i - x_j||_inf = 4 > 0`, and at `lambda = 29` the interval bound is
  `2^2204 > 2^2088 * 3^72`, true in integers. An integer search over `lambda <= 60`
  shows **`lambda = 29` is the smallest scale at which the bound closes**, so the
  constant in item 4 is sharp for this method.

### A.2 Lens 2 — imports

The route declares `requires: []` and cites nothing external. Its only non-elementary
ingredient, Schoenberg's `K -> K^alpha`, is proved from the Schur product theorem and
the Bernstein representation inside Step 4, so there is no citation to mis-quote. The
one import the route *names and refuses* is Misiewicz's theorem (positive definite
functions of `||x||_inf` on `R^3` are constant), which is correctly flagged as **not**
used; it is also the only thing that would extend item 2 to all `beta > 0`. Honest.

**The numerical core, re-derived from scratch.** `audit_linf_certificate.py`:

- Largest eigenvalue of `l^inf^beta` on the zero-sum subspace (a cnd kernel has it
  `<= 0`):

  | grid | `beta = 1` | `1/2` | `1/4` | `1/8` |
  |---|---|---|---|---|
  | `{-1..1}^3` | `+1.414214` | `0` | `0` | `0` |
  | `{-2..2}^3` | `+8.166330` | `+0.677188` | `0` | `0` |
  | `{-5..5}^3` | `+180.025012` | `+13.481175` | `+0.767118` | `0` |

- An integer zero-sum `c` derived from the top eigenvector, with distance-class sums
  `N_d` computed as exact integers and `Q = sum_d N_d d^beta` bounded **below** by
  rational interval arithmetic: for each `d` a rational `a_d <= d^{1/4}` is certified
  by the integer comparison `a_d^4 <= d`, and `Qlow = sum_{N_d>0} N_d a_d +
  sum_{N_d<0} N_d b_d`. Result on `{-5..5}^3` at `beta = 1/4`:
  `Q in [+7.671182e11, +7.671182e11]`, **positive with no floating point in the final
  inequality**. The kernel is therefore not cnd there.
- The lane's three stored certificates were re-verified the same way: every stored
  `N_d` was reproduced exactly, and each `Q0` confirmed positive by interval
  arithmetic independent of the lane's 60-digit `Decimal` code.

### A.3 Lens 3 — calibration: does it prove too much?

**The decisive test is 1V.** Farley proved `1V` has the Haagerup property, so a proper
cnd function exists there; if the route's mechanism transplanted to `n = 1` it would
be refuted on the spot. It does not, and the reason is one line:

> In `V`, two cylinder partitions of `C` with `a` and `b` pieces refine to at most
> `a + b - 1` pieces (the union of a binary tree with `a` leaves and one with `b`
> leaves has at most `a + b - 1` leaves). Hence `L(gh) - 1 <= (L(g)-1) + (L(h)-1)` and
> `L(x^k) - 1 <= k (L(x) - 1)`: leaf count grows **linearly**.
> For `n >= 2` two brick partitions refine to as many as `a b` pieces, and the baker
> map attains it: `L(b_w^k) = 2^k + O(1)`.

Checked (`audit_calibration_1v.py`): subadditivity holds on 400 random pairs of `V`;
the most expanding element sampled has `L(g^k) = 3k + 2`; and for three
disjoint-support copies of `x_0` in `V` the leaf count is additive over the pieces on
`720` of the `729` elements of `{-4..4}^3` (the nine exceptions are the degenerate
exponent-`0` merges), giving exactly

```
L(g(w)) = ||w||_1 + 6      (e.g. w = (4,4,4): L = 18, while 2^||w||_inf = 16 and rising)
```

So in `1V`, `log L(g(w)) = log ||w||_1 + O(1)`: **slowly varying, index 0**, which is
precisely the case item 2 excludes (`beta >= 1/4`) and the claim's own "Untouched"
paragraph names. The obstruction is a genuine `n >= 2` phenomenon. The same reasoning
covers the other calibration worlds asked for: SFT full groups and Nekrashevych groups
act on a one-dimensional Cantor set, where a refinement is `a + b - 1`, so no cyclic
subgroup has exponential brick growth and the hypothesis of item 2 is never met.

**Second calibration, inside nV.** The obstruction is also not too strong there. It
leaves index-`0` functions alone, and `log D` is a *proper* index-`0` function on `nV`
(`{g : D(g) <= c}` is finite). So item 2 does **not** rule out a proper cnd function
of the shape `log D`, and the claim does not say it does. The route's honest scope —
"a proper cnd function on `nV` must see the pieces of a diagram additively, not
through their maximum" — is exactly what the argument delivers.

### A.4 Two amendments the audit recommends (neither weakens the claim)

**(i) The `+ M(1 - delta_e)` clause is redundant, and the theorem is stronger without
it.** In Step 5.2 the perturbation enters only as `- M sum c_x^2`, a constant, which
is divided by `G(lambda) -> infinity`. The same is true of **any** bounded
`b: nV -> R`, since the change in `Q(lambda)` is at most `sup|b| (sum_x |c_x|)^2`.
So item 2 may be stated as:

> under the same hypotheses, `psi + b` is not conditionally negative definite for
> **every bounded** `b: nV -> R`.

This is what one actually wants against Haagerup, where candidate proper cnd functions
are only specified up to a bounded error.

**(ii) `beta >= 1/4` can be lowered to `beta >= 3/20`.** By Step 4 a single certificate
at index `beta_0` kills every `beta >= beta_0`, so the threshold is limited only by the
reach of a finite grid — and the claim's own note ("grids up to `{-7..7}^3` show no
failure at `beta = 0.1`") tested only `beta = 0.1`. Scanning intermediate indices
(`audit_beta_range.py`, largest eigenvalue on the zero-sum subspace; `0` means `< 1e-12`
in modulus):

```
 k   pts    beta=0.25    beta=0.2     beta=0.175   beta=0.15    beta=0.125  beta=0.1
 1     27   0            0            0            0            0           0
 3    343   0            0            0            0            0           0
 4    729   +1.274e-01   0            0            0            0           0
 5   1331   +7.671e-01   +5.719e-02   0            0            0           0
 6   2197   +1.744e+00   +5.684e-01   +1.298e-01   0            0           0
 7   3375   +3.136e+00   +1.296e+00   +6.199e-01   +8.839e-02   0           0
 8   4913   +5.026e+00   +2.281e+00   +1.283e+00   +5.057e-01   0           0
```

Two exact integer certificates were extracted and verified by the same rational
interval arithmetic (no floating point in the final inequality):

- `beta_one_fifth_certificate.json`, `beta = 1/5` on `{-5..5}^3`, `Q >= 5.71884e10 > 0`;
- `beta_three_twentieths_certificate.json`, `beta = 3/20` on `{-7..7}^3`,
  `N_d = (18840324551640, 37227187669834, 14651101424060, -44528036474112,
  -92504838263252, -86030735432372, -25354048571764, 48925805945548, 89940760071264,
  78376337143954, 31547932916520, -14779455177398, -33884959363504, -23427376372832)`,
  `Q >= 8.83909e10 > 0`.

So items 2 and 3 hold verbatim with `1/4` replaced by `3/20`, and in particular
`(log L)^{3/20}` and `D^{3/20}` are killed too. The pattern (first positive grid size
`k = 4, 5, 6, 7` for `beta = 1/4, 1/5, 7/40, 3/20`) says the threshold is driven purely
by grid size, so `beta < 3/20` is a computational, not a structural, limit;
**Misiewicz's theorem remains the clean way to reach all `beta > 0` in one step.**

**Verdict: ESTABLISHED stands.**

---

## B. `nv-point-germ-groups-embed-in-zn-by-slope`

### B.1 Lens 1 — the first step that does not follow

Each of items 1-6 was re-derived; all follow.

- **Item 1, zero slope.** On a brick `B = [u] ∋ x` of shape `>= D_g`, `gB` is the brick
  of shape `|u| - s(g,x) = |u|` containing `gx = x`, hence `B` itself; two bricks of
  the same shape containing a common point coincide, so `g phi_B = phi_B` and `g` is
  the identity on `B`. Correct.
- **Item 1, rank.** If `s(g,x)_i = d_i < 0` then `v_i = u_i q` with `|q| = -d_i >= 1`,
  both prefixes of `x_i`, and `gx = x` forces `t_i = q t_i`, i.e. `x_i = u_i q^infty`.
  The `d_i > 0` case goes through `g^{-1}`, whose slope at the fixed point `x` is
  `-d`. Correct.
- **Item 2.** With `Gamma = G <= nV`, `X = Z`, `iota = id`, this is exactly the
  statement needed in item 3. `ker h_x` is contained in the subgroup that is locally
  trivial *in `Z`*, so `Germ_{Gamma,X}(x)` is a quotient of `im h_x <= Z^n`. Correct.
  (Worth spelling out for a reader: the germ group of an action depends only on the
  image of `G` in `Homeo(Z)`, because the kernel of `G -> Homeo(Z)` is locally
  trivial. That is why "no minimal set of a subgroup of `nV` is conjugate to the
  `SL_3` system" follows even though a conjugacy gives a surjection `G -> Gamma`
  rather than a homomorphism `Gamma -> nV`.)
- **Item 3.** `M_A = diag(1, A)` fixes `[1:0:0]`; `M_A` is scalar only if `A = lambda I`
  with `lambda = 1` and `det A = 1`, i.e. `A = I`. A non-scalar `M in GL_3(Q_p)` fixes
  no nonempty open subset of `P^2(Q_p)`, since its fixed set is the finite union of
  the projectivised eigenspaces `P(ker(M - lambda))`, `lambda in Q_p`, each a proper
  projective subspace, hence closed and nowhere dense. So `SL_2(Z[1/p])` injects into
  the germ group, which is therefore non-abelian. `P^2(Q_p)` is compact and totally
  disconnected, so item 2 applies. Correct.
- **Item 4.** Canonicity plus the sub-brick rule gives `g^k z = (w_i u_i^k t_i)_i`,
  which converges; `Z` is closed and `g`-invariant, so the limit `p` is in `Z n B`,
  `g p = p` because `u_i u_i^infty = u_i^infty`, and `s(g,p) = -|u| != 0`. Correct.
- **Item 5.** `gB` has shape `k - d >= k` and contains `z`, so it sits inside `B` and
  is strictly smaller since `d != 0`; the `d >= 0` case uses
  `s(g^{-1}, z) = -s(g, z)`. Correct.
- **Item 6.** Correct, and see B.2.

**Mechanism check in 2V** (`audit_germ_slope.py`), on the independent implementation:

```
s(gh,x) = s(g,hx) + s(h,x) on 300 random (g,h,x): violations 0
zero slope with image brick = domain brick => identity there: 1707 bricks, violations 0
item 4, x_0 in coordinate 1: B = [0] x C, gB = [00] x C, u = ("0", "");
        p = (0^infty, .) is fixed, s(g,p) = (-1, 0)          [item 4 predicts (-1,0)]
item 4, x_0 in both coordinates: B = [0]x[0], gB = [00]x[00];
        p fixed, s(g,p) = (-1,-1)                            [item 4 predicts (-1,-1)]
item 5, saddle: b = baker(""), x = (0^infty, 0^infty) is fixed with s(g,x) = (1,-1)
```

The last line realises item 5's remark that saddles exist and need `n >= 2`.

### B.2 Lens 2 — imports

The route names one import, Delorme-Guichardet, "cited exactly as in"
`research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md` (Bekka-de la
Harpe-Valette, *Kazhdan's Property (T)*, Theorem 2.12.4). The artifact exists and its
Section 0 states the notation, the sub-brick rule, the deep-brick rule and the slope
cocycle that the route uses, so the notation reference resolves.

Two remarks on the hypothesis match.

- BdlHV 2.12.4 is an *equivalence* only for `sigma`-compact locally compact groups;
  the direction used here, `(T) => (FH)`, holds for every topological group. `L <= nV`
  is countable discrete, hence `sigma`-compact locally compact, so either reading is
  safe. The artifact's parenthesis "(for countable discrete groups)" is the right
  guard.
- **The import is not needed at all.** Item 6 asks only that a homomorphism
  `L -> Z^n` vanish. A group with property (T) has finite abelianisation
  (BdlHV Corollary 1.3.6), so `Hom(L, Z^n) = 0` immediately. Recording this makes the
  route `requires`-free and removes its single citation risk.

One statement is looser than the proof. The frontmatter title says germ groups are
"abelian **of rank at most n**", while item 2's conclusion is a *quotient* of a
subgroup of `Z^n`, which may have torsion (an element can be locally trivial on `Z`
without being locally trivial on `C^n`). The body is precise ("abelian and generated
by at most `n` elements"); read "rank" as torsion-free rank. Nothing downstream uses
freeness — item 3 uses only "abelian".

### B.3 Lens 3 — calibration: does it prove too much?

The theorem is a statement about `nV` itself, so the test is whether some group known
to act on a Cantor set with a *non-abelian* germ group is known to sit inside `nV`
with that action realised on a closed invariant subset.

- **`1V`.** Germ groups of `V` at a point are `Z`, detected by the slope; the `n = 1`
  case of item 1 is the classical statement. No conflict.
- **SFT full groups.** For a full shift the topological full group is `V`; in general
  the isotropy of the groupoid at a point is generated by the return-time shift, and
  the germ group is cyclic. Abelian; no conflict.
- **Nekrashevych groups and self-similar groups.** These are the sharp test, because
  `V_G(X)` is designed to have germs coming from `G`. The theorem predicts that no
  such group whose germ group at some point is non-abelian can act on a closed
  invariant subset of `C^n` through `nV`. That is consistent with what is known, and
  is not vacuous: a self-similar group whose sections never become trivial (the
  Grigorchuk group, and any group of infinite-state or non-eventually-trivial
  automata) is not a subgroup of `V` at all, precisely because elements of `nV` are
  *finite brick* maps. The Grigorchuk group's own germ group at `1^infty` is the Klein
  four group, which is abelian, so it is not even a candidate counterexample; the
  theorem bites on decorations with non-abelian germs, e.g. Rover-type groups where a
  slope element conjugates the finite germ decorations.
- The theorem does **not** separate `nV` from actions with virtually cyclic point
  stabilisers, e.g. boundary actions of hyperbolic groups. The claim says exactly this.

**Verdict: ESTABLISHED stands.**

---

## C. What this leaves open on the route to `zaremsky-2-07-brin-thompson-nv-haagerup-or-t`

Both claims survive, so the two obstructions they encode stay on the board:

1. A proper cnd function on `nV` cannot be (asymptotically) a regularly varying
   function of positive index of `log L` or of `D`. After amendment (ii) the excluded
   range is `beta >= 3/20`; `0 < beta < 3/20` is open by this route, and **importing
   Misiewicz's theorem (positive definite functions of `||x||_inf` on `R^3` are
   constant) would close it for all `beta > 0`** — that is the cheapest remaining win
   on this node and is now the only thing standing between the claim and "no positive
   index at all".
2. The surviving shapes are: index-`0` functions of the diagram (e.g. `log D`, which
   *is* proper), and functions additive over disjoint supports on the `Z^3` of baker
   maps. Any Haagerup attempt for `nV` should build one of those two.
3. `nv-point-germ-groups-embed-in-zn-by-slope` item 3 stands, so the `SL_3(Z[1/p])`
   action on `P^2(Q_p)` — the canonical measure-free Kazhdan minimal system — really
   is excluded from `nV`, and the open hole
   `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures` cannot be
   refuted by transplanting it.
