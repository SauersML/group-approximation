# Adversarial audit of two unrefereed F claims (2026-09-18)

Agent `e2-w2-audit-f`, wave `swarm-0917`. Both targets landed **ESTABLISHED** on `main` in the
2026-09-17 wave with their referee votes never cast. This is the missing referee pass. No new
mathematics is claimed here; the only outputs are a verdict per claim, a list of defects found, and
two re-derivation scripts.

Targets:

- `thompson-f-binomial-multipliers-see-every-conjugate` (+ its route
  `thompson-f-binomial-multipliers-see-every-conjugate-proof`)
- `f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent` (+ its route
  `f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent-proof`)

Three lenses were run on each: (1) gaps — the first step that does not follow; (2) hypotheses and
citations — does each import say exactly what is used, with the same quantifiers; (3) calibration —
which step fails on a neighbouring world, and does the proof use what separates `F` from it. Every
artifact script was re-run and its numbers compared against the claim text.

**Verdict: both survive. Both stay ESTABLISHED.** Six defects were found, all of them in prose or in
a script docstring; none touches a theorem item or a kill-list item. The most consequential is
finding **A6** below, a scope word ("equivalent") in a commentary paragraph of the first claim.

Audit scripts (new, this pass):

- `experiments/f-audit-lenses-2026-09-17/audit_ore.py`
- `experiments/f-audit-lenses-2026-09-17/audit_koopman.py`
- `experiments/f-audit-lenses-2026-09-17/audit_ore.log`,
  `experiments/f-audit-lenses-2026-09-17/audit_koopman.log`

---

## 1. `thompson-f-binomial-multipliers-see-every-conjugate`

### Lens 1 — gaps

Every step of the route was re-derived independently. Nothing failed. The checks that are not
one-line verifications:

- **Step 0.** `1 + lambda g = lambda(g - mu)` with `mu = -1/lambda` is correct. With `g` of infinite
  order, `n -> g^n w` is a bijection `Z -> <g>w`, the restriction of `(g - mu)u` to that coset is
  `(t - mu) U_C(t)` in `K[t,t^-1]`, and `t - mu` divides a Laurent polynomial iff it vanishes at
  `mu != 0`. `supp y` meets only finitely many cosets, so the "if" direction really does produce a
  finitely supported `u`. The consequence `g^a y - mu^a y in J` is correct for `a < 0` as well:
  `g^a - mu^a = -mu^a g^a (g^{-a} - mu^{-a})` and `K[<g>]` is commutative, so the factor `(g - mu)`
  can be moved to the left.
- **Step 2, the beta identity.** The normal form `g^m t_0 c` on the double coset `D = <g> t_0 V` uses
  exactly `V ∩ t_0^{-1}<g>t_0 = 1`; distinctness of the `c_t` uses exactly that `b` is reduced; and
  the computation `eps_{t_0 x}(b v) = (beta v)(x)` is correct as written. This is the one place where
  a sign or an index slip would be invisible on a reading, so it was re-derived numerically as well
  (below).
- **Step 3.** `Fix(h^n) = Fix(h)` for `n != 0` holds because an increasing homeomorphism of `[0,1]`
  with a periodic point fixes it. `Fix(t^{-1} g^n t) = t^{-1} Fix(g)`, hence
  `Fix(V_v) ⊆ Fix(t^{-1} g t)`.
- **Step 4.** `x -> <g> w x` is injective on `A` exactly because `A ∩ w^{-1}<g>w = 1`; `Y_D` is then
  a genuine element of `K[A]`, and `eps_{wx}(ya) = (Y_D a)(x)`. The peeling argument needs
  `J != R`, which holds since `eps_1(1) = 1`. The bump count uses torsion-freeness of `F` to force
  `m != 0` in `h^n = w^{-1} g^m w`; without it the conclusion would be false.
- **Step 5.** `b g^a = g^a phi^a(b)`, `K[V] ∩ J = 0` (because `<g>x` meets `V` only in `x`), and both
  directions of the dependence criterion are correct, including the re-indexing by `phi^k`.
- **Step 6.** `V = <g_1> ⋉ F_c(p,q)` does satisfy the hypotheses of item 3: `g` normalizes it,
  `g^{-1} g_1 g = g_1` because `g_2` commutes with `g_1`, and `V ∩ <g> = 1` because every element of
  `V` is the identity near `q` while `g^n = g_2^n` there.

**Numerical re-derivation.** `audit_ore.py` implements `F` exactly, as PL homeomorphisms of `[0,1]`
with dyadic breakpoints and power-of-two slopes (so group equality is tuple equality and `K[F]` with
`K = Q` is exact), takes `g = g_1 g_2` with bumps `(0,1/2)` and `(1/2,1)` and `lambda = 2`, and
re-derives on random data:

| check | result |
|---|---|
| Step 0 coset test, both directions, and `g^a y - mu^a y in J` | PASS |
| Step 1, `b - b°` in `J` and `b°` meets each coset once | PASS |
| Step 2, `eps_{t_0 x}(bv) = (beta v)(x)`; and `bv` in `J` for a transverse `t_0` | PASS, 30 random `(b,v)` pairs, 0 landed in `J` (theorem says 0) |
| Step 4, transverse saturation, and no unit times a product of one-bump twisted binomials in `J` | PASS |
| Step 5 congruence | PASS |
| `supp h^n = supp h`, conjugation preserves the bump count | PASS |
| Step 6 structural facts for `V = <g_1> ⋉ F_c(p,q)` | PASS |

The falsification search in row 3 is the sharp one: it looks for the counterexample the support
theorem forbids and finds none.

### Lens 2 — hypotheses and citations

The route quotes exactly one outside input: left-orderability of `F`, so that `K[V]` is a domain for
every `V <= F`, cited to derivation step 2 of `thompson-f-amenable-iff-group-ring-is-ore`. That is
what Steps 2, 4 and 5 use, and nothing more. Everything else, including the coset test that the
setting attributes to Step 1 of `thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof`, is
re-proved in Step 0, so the route does not inherit that node's trust surface.

Cross-consistency with the established neighbours, all checked, none contradicted:

- `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof`, closing Remark. With `b = 1`,
  `V = Stab_F(z)`, `g = c`, item 1 gives `Stab_F(z) ∩ <c> != 1`, i.e. `c^n(z) = z` for some `n != 0`,
  i.e. `c(z) = z`. Contrapositive: `c` moving `z` kills every multiplier in `K[Stab_F(z)]s`. That is
  the Remark verbatim.
- `thompson-f-binomials-meet-ideals-with-separated-conjugates`. There `supp b ⊆ V_Z s` and the bumps
  of `t^{-1} g t` lie strictly between consecutive `z_i`, so every conjugate lies in `V_Z` and fixes
  `Z`. The necessary condition of item 1 is met, not violated.
- `thompson-f-twisted-x0-binomial-is-ore-with-every-element` (ESTABLISHED, every `b`). For `g = x_0`
  the fixed points are `0` and `1`, which no `t in F` maps into the moved set `(0,1)`, so item 1's
  obstruction is vacuous there. No collision.
- `thompson-f-one-bump-binomials-have-common-multiples`, item 2(c). That asserts
  `P R ∩ c R != 0` for a product `P` of one-bump twisted binomials; the audited item 2 asserts
  `P ∉ J`. Different statements, both true.

### Lens 3 — calibration

- **Thompson's `T`.** Three separate steps die, and they are exactly the steps that carry the
  `F`-specific corollaries. (i) `K[T]` is not a domain: `T` has torsion, so
  `(1-r)(1+r+...+r^{n-1}) = 0` for a rotation `r` of order `n`, and the domain hypothesis of Steps 2,
  4, 5 fails for any `V` containing torsion. (ii) `Fix(h^n) = Fix(h)` fails: an element of `T` with
  rotation number `1/2` has no fixed point while its square does, so Step 3's translation of the
  support theorem into fixed points collapses. (iii) Step 4's bump count uses torsion-freeness to
  force `m != 0`. The general items 1–3 survive in `T` under their stated hypotheses (they never use
  orderability of the ambient `G`), and the claim confines the fixed-point and bump-count corollaries
  to `G = F`. Correctly scoped.
- **The positive monoid / `F^+`.** Dies at Step 0, first line: the coset test needs the bijection
  `Z -> <g>w`, which needs `g^{-1}`. Step 2 also uses `J s^{-1} = J` and
  `V_v = <x y^{-1} : x,y in supp v>`, both of which need inverses.
- **`PL_+([0,1])`, Cleary's `F_tau`, and any left-orderable subgroup of `Homeo_+([0,1])`.** Nothing
  dies: the proof uses only left-orderability (so subgroup rings are domains), torsion-freeness
  (automatic in `Homeo_+` of an interval), and that conjugation preserves the number of components of
  the support. So the theorem is true in all of them. This is not a defect — the statement is true
  there — but it does mean the claim's content is not `F`-specific; only the kill list is, through
  the `F` nodes it names.
- **Non-unimodular / locally compact worlds.** Out of scope: `J` and the coset test are statements
  about a discrete group ring.

### Defects found (none refuting)

- **A1.** "`supp g`" is used throughout for the *moved set* `{x : g(x) != x}`, not for its closure.
  A bump endpoint of `g` lies in the closure but is fixed, so the sentence "if some `t` in `supp b°`
  maps a point `z` into `supp g`, no nonzero multiplier ... exists" must be read as "maps `z` to a
  point moved by `g`". Step 6 uses it consistently in that sense
  (`(p,q) \ {m} = supp g`), so no step breaks.
- **A6 (the substantive one).** Under *What survives, as a precise decomposition*, the claim says the
  "Opposite orientations" reduction "is equivalent, for `b` in `K[V]`, to zoom-orbit dependence".
  Item 3, which is what supplies it, is an equivalence only for multipliers *inside* `K[<g>V]`:
  "some nonzero `v` **in `K[<g>V]`** has `b v` in `J` iff ...". The Ore question allows `v` anywhere
  in `R`. So the established direction is
  *zoom-orbit dependence ⟹ `(1 + lambda g) R ∩ b R != 0`*, which is the direction the decomposition
  needs; the converse is open. The word "equivalent" overstates it by one direction. Separately, the
  "Opposite orientations" reduction it refers to is itself an open attempt of
  `thompson-f-every-twisted-binomial-is-ore-with-every-element` and carries a recorded gap
  (`notes/thompson-f-is-amenable-swarm-2026-09-16.md`, "Caveat on the hole's Opposite orientations
  attempt"), so the sentence should not be read as reducing that attempt to a single finite
  condition. The theorem items 1–3 and the whole *What this kills* list are unaffected.

---

## 2. `f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent`

### Lens 1 — gaps

Re-derived step by step; nothing failed. The places where a slip would be invisible:

- **(P0).** `Q = 1_E P 1_E` is self-adjoint and positivity preserving, so `|<Qf,f>| <= <Q|f|,|f|>`
  and `||Q|| = sup{<Qf,f> : f >= 0} = max spec Q`. Used four times; correct.
- **Section 1.** The induction gives
  `Q^n 1_E = Σ mu(h_1)...mu(h_n) 1_{E ∩ h_n E ∩ ... ∩ h_n...h_1 E}`; `gE = {w : w(g x_0) = 0}`
  (from `(gw)(x) = w(g^{-1}x)`); `h_n...h_k = g_n g_{k-1}^{-1}`, so the intersection is the event
  that `w` vanishes on `g_n O_n`, a set of size `|O_n|`. Even-time lower bound by a spectral
  projection, odd times by monotonicity of `|O_n|`. All correct.
- **Section 2.** `||pi(h)u - u||_1 <= ||pi(h)f-f||_2 ||pi(h)f+f||_2 <= 2||pi(h)f-f||_2`, then
  Cauchy–Schwarz over `mu`, layer cake, and the averaging step. The averaging step needs one remark
  the text leaves implicit: on `{t : m(A_t) = 0}` the integrand vanishes identically, so the
  selected `t` can be taken with `m(A_t) > 0`. That is immediate, not a gap.
- **Section 3.** `P_R` is irreducible on `B_R` because stripping the first letter of `g = s_1...s_r`
  stays in `B_R`; `P_R^{2n}(e,e) >= lambda_R^{2n} phi_R(e)^2`; the event
  `{g_1,...,g_{2n} in B_R}` forces `O_{2n} ⊆ B_R x_0`; `lambda_R` is the max Rayleigh quotient of
  `lambda(mu)` over functions supported in `B_R`, nondecreasing, with supremum `rho`.
- **Section 4.** Walsh characters satisfy `pi(g) w_A = w_{gA}`; `|c|^2 <= ||1_E||^2 = 1/2`;
  `|c|^2 + rho_0^+(1-|c|^2) <= (1+rho_0^+)/2` because `rho_0^+ <= 1`.
- **Section 5.** The ray counts are exactly `binom(N-1,k-1)` for `x_0^{±1}` and `0` for `x_1^{±1}`,
  giving Rayleigh quotient `>= 1 - k/N`.
- **Section 6.** `O_n ⊆ D_C` iff `1/2 in T_i = g_i D_C` for all `i <= n`; the killed chain is
  Markov; `P(O_n ⊆ D_C) <= 2^{2^C} E 2^{-|O_n|}`; the depth recursion `d(st) <= max(d(t),2)+1` holds
  for all eight piecewise formulas, giving `d(g.(1/2)) <= |g|+2`.

**Numerical re-derivation.** `audit_koopman.py`:

| check | result |
|---|---|
| (A) `E 2^{-|O_n|} = <Q^n 1_E, 1_E>` exactly in `Q`, for `S_3` on 3 points, `S_4` on 4 points and `Z/5` regular, `n <= 5` | PASS (all three, all `n`) |
| (B) `|x_0^{±1} Phi_N \ Phi_N| = binom(N-1,k-1)`, `|x_1^{±1} Phi_N \ Phi_N| = 0`, Rayleigh `>= 1-k/N`, `N <= 8`, `k <= 4` | PASS |
| (C) `d(g.(1/2)) <= |g|+2` by BFS to radius 7 | PASS (observed max depth is `|g|+1`, so the bound has one unit of slack) |
| (D) ball Perron eigenvalues of `F_2` increase and stay below `rho = sqrt(3)/2` | PASS (`0.500, 0.661, 0.733, 0.772, 0.796`) |

(A) is the strongest of these: a finite `X` is a legitimate test because Section 1 uses nothing about
`X` beyond transitivity, and the identity is checked in exact rational arithmetic against a brute
force over all `3^n` (resp. `2^n`) walk paths.

### Lens 2 — hypotheses and citations

All four `requires` are ESTABLISHED and say exactly what is used:

- `thompson-f-norm-bound-from-hhr-exact-moments`: "`||P|| > 225383/250000 = 0.901532`" for
  `P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4`. That is `mu` uniform on `{x_0^{±1}, x_1^{±1}}`, the
  measure used, and `-log 0.901532 = 0.1036597... < 0.10366` as stated. It is a *lower* bound on
  `rho`, which is the direction needed for an *upper* bound on `Lambda`.
- `kesten-amenable-stabilizer-uniform-gap`: "for **every** amenable subgroup `H <= A` and every real
  `f in l^2(A/H)`, `sum_{s in S} ||f - sf||^2 >= kappa ||f||^2`" with `kappa = 2|S|(1-rho)`. For `mu`
  uniform on `S` this is `<Pf,f> <= rho ||f||^2`, i.e. top of spectrum `<= rho` on each
  quasi-regular summand. That is exactly what Section 4.4 needs, and it needs `mu` uniform on a
  finite symmetric generating set, which the claim's item 4 hypothesises.
- `f-dyadic-ea-iff-inverted-orbit-confinement`, condition 2: "`lim -(1/n) log E(2^{-|O_n|}) = 0`",
  with the same left walk `g_n = h_n...h_1`, the same `O_n`, and the same class of `mu`. That is
  `Lambda = 0` verbatim.
- `thompson-f-amenable-iff-dyadic-action-extensively-amenable`, item 1: "`F` is amenable if and only
  if the action `F ↷ D` is extensively amenable."

The chain of Section 6.5 therefore closes: `F` amenable `=> rho = 1 => sup_C lambda_C = 1 =>
||Q|| = 1 => Lambda_F = 0 =>` EA `=> F` amenable.

The "Correction" bullet quotes `research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md`
accurately: that file says bounded-depth confinement costs "an exponential probability with a rate
that does not go to `0` with the band". By item 6 that is `sup_C lambda_C < 1`, i.e. exactly the
nonamenability of `F`, so it cannot serve as an obstruction. The correction is right.

### Lens 3 — calibration

- **Thompson's `T`.** Section 5 is where `F` is used, and it uses it correctly: the Følner sets are
  `k`-subsets of the ray `{2^{-1},...,2^{-N}}`, and the argument needs a generator that is the
  *identity on a half-interval* (`x_1` on `[0,1/2]`) and one that *shifts the ray* (`x_0`). `T`'s
  rotation generator is the identity on no interval and does not preserve any such ray, so the
  count breaks at "`x_1^{±1} Phi_N = Phi_N`". This is the right kind of break: the class kill of
  item 5 is a statement about `F`'s standard generating set, and the claim says so.
- **`PSL_2(Z) ↷ P^1(Q)`, the calibrator inside the claim.** Here `rho_k <= rho < 1` by item 4,
  because a finite-set setwise stabilizer contains the pointwise stabilizer with index at most
  `|A|!`, and the pointwise stabilizer sits inside a conjugate of `Stab(∞) ≅ Z`. So the Walsh-level
  method *does* work on a nonamenable group with the same tree-of-horocycles Schreier picture. The
  kill of item 5 is therefore specific to `F`, not a triviality — this is the calibration the class
  kill needed, and the claim supplies it.
- **Finite-set stabilizers in `F`.** Section 5.4's observation that they contain a copy of `F`
  (elements supported in a dyadic interval disjoint from `A`) is what removes the item-4 squeeze for
  `F`. Correct, and it is the exact structural difference from the `PSL_2(Z)` calibrator.
- **Non-unimodular groups.** Out of scope: the setting fixes a countable discrete group, where
  unimodularity is automatic and Kesten's 1959 criterion applies as cited.

### Artifact re-run (all bit-for-bit identical to the recorded logs)

Re-run in this worktree, same defaults and seeds as recorded:

| script | invocation | result |
|---|---|---|
| `psl_return.py` | `--steps 26` | every row identical to `psl_return.log` through `t = 26`, including `p_32`-style roots `0.57735 ... 0.86052` |
| `cloning.py` | `--n 1000` (seed 1) | every line identical to `cloning_main.log`, including `inexact halvings: 0` |
| `band_long.py` | `--Cmax 8 --only F` | identical to `band_F.log` |
| `band_long.py` | `--Rmax 9 --only PSL` | identical to `band_PSL.log`, including `inexact halvings 0` |
| `lambda_long.py` | `--which F`, then separately `--which PSL` | identical to `lambda_F.log`, `lambda_PSL.log` |

Full transcript: `experiments/f-audit-lenses-2026-09-17/rerun_of_recorded_artifacts.log`.

Every number quoted in the claim body was checked against these logs:
`0.0577` at `n=1000`, `0.0462` at `n=4000`; the band table
`0.34, 0.20, 0.15, 0.11, 0.087, 0.082, 0.06`; the PSL ball-band row
`0.294 ... 0.045`; `Λ̂_PSL` cumulative `0.052`, late windows `0.047`; `F_2` `0.298`, `Z^3` `0.191`,
lamplighter `0.120`; and the rigorous `F_2` squeeze `0.06934 <= Λ <= 0.14384`. All match.

### Defects found (none refuting)

- **B1.** Section 6.4 of the route writes "`lambda_{R+2} >= lambda_R ↑ rho(F,mu)`", where the left
  `lambda` is a *band* exponent of Section 6 and the right `lambda_R` is the *ball* Perron eigenvalue
  of Section 3. Two different objects with one symbol. The claim text disambiguates correctly
  (`lambda_R^{ball}`); the route does not.
- **B2.** The base point of the general setting is called `x_0` and a generator of `F` is also called
  `x_0`; item 6 then writes "`x_0 = 1/2`". Resolvable from context, but the collision is real.
- **B3.** The bullet "*Quantifier level*" reads "It is now the single number `||1_E P 1_E|| = 1`",
  which parses as an assertion that `||Q|| = 1`, i.e. that the open target is true. It means "the
  target is now the single statement `||Q|| = 1`". The claim's own `distinct_from` says it does not
  decide it, so no reader of the whole node is misled, but the sentence as written asserts more than
  is proved.
- **B4.** `psl_return.py`'s docstring says its output is "for the calibrator lower bound
  `Lambda >= -log((1+rho)/2)`". It is not: `p_{2n}^{1/2n}` is a *lower* bound for `rho`, and a lower
  bound for `rho` gives an *upper* bound `Lambda <= -log rho`, which is how the claim body actually
  uses it (`Λ_PSL <= 0.1331`). The quantitative lower bound would need an upper bound on `rho`, which
  no artifact computes; `Λ_PSL > 0` is qualitative, from nonamenability of `PSL_2(Z)`. Docstring
  only — the claim body is correct.
- **B5.** The band table lists rate `0.15` at `C = 4`, where `band_F.log`'s last window is `0.1556`
  and the cumulative is `0.1432`. Within "late window rates", but the strictest reading of the log
  is `0.16`. Cosmetic.
- **B7 (reproduction provenance).** `lambda_F.log` and `lambda_PSL.log` were produced by two
  *separate* invocations, each with a fresh `random.Random(11)`; the json files confirm it
  (`lambda_F.json` carries only the key `F_dyadic`, `lambda_PSL.json` only `PSL_P1Q`). The script's
  default `--which both` runs `F` first and then `PSL` on the *continued* rng stream: it reproduces
  `lambda_F.log` exactly but gives a different PSL run (cumulative `0.0535`, windows
  `[0.0642, 0.0577, 0.0541, 0.0532, 0.0529, 0.0515, 0.0481, 0.0466]`). The same applies to
  `band_long.py`, whose two logs come from `--only F` and `--only PSL`. So a referee must re-run
  each model separately; the defaults do not reproduce both recorded logs at once. Model by model
  everything is bit-for-bit exact, so no number in the claim changes — but the scripts do not record
  the flags used, which cost this audit one wrong-looking run.
- **B6 (an unused sharpening, recorded so it is not lost).** The same `psl_return.log` supports a
  ceiling 2.3 times better than the one the claim quotes. `p_{2n} = ∫ |t|^{2n} dν(t)` for the
  spectral measure `ν` of `P` at `δ_e`, so by Cauchy–Schwarz `p_{2n}^2 <= p_{2n-2} p_{2n+2}`: the
  ratios `r_n = p_{2n}/p_{2n-2}` are nondecreasing with limit `rho^2`, hence `sqrt(r_n) <= rho` for
  every `n`. The last printed column of `psl_return.log` is exactly `sqrt(r_n)`, and at `t = 32` it
  is `0.94459`, giving `rho(PSL_2(Z), {S,T,T^{-1}}) >= 0.94459` and `Λ_PSL <= 0.05706`, against the
  claim's `0.1331` from `p_32^{1/32} = 0.87536`. This changes no conclusion — the claim's reading of
  the numerics is that finite-size estimates cannot separate the two worlds, and `Λ̂_PSL ≈ 0.047` sits
  below `0.05706` as well — but it is the sharper number the artifact already contains.

---

## 3. Bus record

`bin/cairn-live verdict <id> --outcome survives` posted for both ids under agent `e2-w2-audit-f`,
wave `swarm-0917`.
