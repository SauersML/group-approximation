# hl-nh-deligne-extension: does character rigidity with Deligne force central collapse?

Lane date: 2026-09-14. Target: `non-hyperlinear-group`, through Deligne's triple cover
`E_3 -> Sp_4(Z)` and its Torelli-scalar form on `Mod(S_2)`. Status: unreviewed commentary, except
where a node is named as the source of a result.

## 0. Verdict

- **Not decided.** `deligne-central-mark-hs-collapse` and
  `deligne-stable-triple-cover-is-not-hyperlinear` remain OPEN.
- **Landed (established, unreviewed):** `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors`
  (E1–E4), a trace dictionary for *exact* representations of `Mod(S_2)`, a conditional converse, and a
  finite-image floor.
- **Landed (OPEN):** `mod-s2-exact-representations-have-a-torelli-scalar-gap`. It is the uniform gap for
  exact models, necessary for the genus-two route and equivalent to it if `Mod(S_2)` is flexibly
  HS-stable.
- **Answer to the brief:** character rigidity and Deligne's finite-quotient theorem do *not* force
  collapse. Section 2 gives the precise escape.

## 1. Sources

No new source was fetched: the MSI master was down at lane start. The inputs of the brief are already
pinned on main, and this lane only consumes those nodes.
- Deligne non-residual finiteness and finite residual: `deligne-universal-cover-lattice-is-non-rf-kazhdan`,
  `deligne-covers-of-sp2g-z-have-finite-residual-2z`.
- Property (T) of the extension: `bdhv-central-extension-property-t`.
- Character rigidity in the sector: `deligne-maslov-sector-traces-are-central-regular`, through
  `deligne-central-regular-trace-classification-proof`, whose citation audit is
  `research/artifacts/deligne-maslov-character-rigidity-and-psd-cone-fence-2026-08-21.md`.
- Two-norm inapproximability: `bdl-deligne-type-two-norm-inapproximability`, which states that as of
  April 2026 hyperlinearity of the real Deligne covers is undecided.
- Frobenius stability and collapse at `g >= 3`: `deligne-symplectic-covers-are-not-schatten-approximated`.
- HS stability and non-hyperlinear extensions: `hs-stability-forces-nonhyperlinear-central-extension`,
  `dv-s-arithmetic-hs-stable-nonhyperlinear-extension`, `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`.
- Uniform stability: `research/artifacts/glmr-2301-00476-verified.md`.

Not re-pinned here, and used only in Section 5 as a heuristic: the Birman–Hilden description of
`Mod(S_2)` and `PMod(S_(0,4)) ~= F_2`.

## 2. Step 2 of the brief: where rigidity and Deligne stop

Let `phi_n` be HS almost representations of `E_3` and `tau` a limit trace.
1. **Rigidity fixes the sector trace.** By `finite-central-hs-sector-decomposition`, `tau` splits by
   central character. By `deligne-maslov-sector-traces-are-central-regular`, the part with `z -> omega`
   is a mixture of `tau_(eta_+)` and `tau_(eta_-)`. So rigidity decides *which* trace a sector model
   converges to. It cannot decide *whether* such models exist.
2. **Deligne kills only finite-dimensional character limits.** By Malcev, a finite-dimensional unitary
   representation of `E_3` kills `z`. So every limit of finite-dimensional characters of `E_3` has
   `tau(z) = 1`, and `||phi_n(z) - I||_2^2 = 2 - 2 Re tr phi_n(z) -> 0`.
3. **The escape.** The sector traces `tau_(eta_+-)` are genuine tracial states. They are not limits of
   finite-dimensional characters of `E_3`, yet nothing in rigidity or in Deligne prevents them from
   being Connes-embeddable. Hyperlinear microstates would live exactly there.
   `deligne-sector-gap-is-exactly-nonhyperlinearity` records that the sector gap is the whole problem.
4. **Amenability is the wrong dividing line.** Every sector trace is non-amenable
   (`deligne-twisted-fibres-have-no-amenable-trace`). But non-amenable Connes-embeddable traces are
   ubiquitous, for instance the regular trace of `Sp_4(Z)`. So "no amenable trace" can't force collapse.

**Conclusion.** Character rigidity plus Deligne reduce collapse to the Connes-embeddability of one
explicit trace, and prove nothing more. Proving collapse needs an input that separates embeddable
non-amenable traces from non-embeddable ones on this algebra. No such input is on main or in the pinned
literature.

## 3. Exponent-1/2 barrier for unnormalized stability inputs (commentary)

- **Setup.** `deligne-hs-metric-ladder` (artifact of 2026-09-13) derives the floor
  `sigma_(1/3)(d) >= delta d^(-1/2)` from Frobenius stability at `g >= 3`.
- **No unnormalized norm does better.** Let `|||.|||` be any unitarily invariant norm with
  `|||X||| >= ||X||_op`, such as a Schatten norm or a Ky Fan norm.
  - A relator defect with a single `-1` eigenvalue has `|||D||| >= 2`, but normalized norm
    `||D||_2 = 2 d^(-1/2)`.
  - So a black-box `|||.|||`-stability theorem, applied to defects, can only exclude tuples with
    `||D||_2` below a constant times `d^(-1/2)`.
- **Schatten check.** For `p > 2`, `||D||_p <= 2^(1-2/p) (d^(1/2) ||D||_2)^(2/p)`. Stability below
  `e < 2` excludes `||D||_2 < 2 (e/2)^(p/2) d^(-1/2)`. The exponent is again `d^(-1/2)`, and the constant
  only shrinks as `p` grows.
- **Consequence.** Improving the exponent requires information about how the defect spreads over a
  positive fraction of the spectrum. This is the normalized content of the problem, not a change of norm.

## 4. New dictionary for exact Mod(S_2) models (landed)

`Mod(S_2)` maps onto `E_3` (TS1). Exact representations of `Mod(S_2)` satisfy every relator. The only
defect is `delta(rho) = ||rho(t_s) - omega^epsilon I||_2`.
- **(E1)** `delta -> 0` iff the characters converge into the pulled-back sector traces. So the uniform
  exact gap says that `tau'_+-` are not limits of finite-dimensional characters of `Mod(S_2)`.
- **(E2)** Vanishing exact defect makes `E_3` hyperlinear.
- **(E3)** Conversely, if `Mod(S_2)` is flexibly HS-stable.
- **(E4)** Finite-image floor `delta >= sqrt(3)/l(N)`.

**Use for construction lanes.** Any *exact* family with `delta -> 0` is a complete hyperlinearity proof
for `E_3`. The families tried so far fail:
- SU(2) quantum representations (`hl-nh-quantum-reps`) have distance to scalars tending to 1;
- finite images need `l(N) -> infinity`.

## 5. No relative spectral gap for Torelli (heuristic, unpinned)

- **Virtual surjection.** `Mod(S_2) -> Mod(S_(0,6))` (Birman–Hilden) and forgetting two marked points
  give a finite-index `M' <= Mod(S_2)` surjecting onto `PMod(S_(0,4)) ~= F_2`, hence onto `Z`.
- **Every such map sees Torelli.** Suppose a homomorphism `M' -> Z` were zero on `K cap M'`. It would factor
  through `M'/(K cap M')`, a finite-index subgroup of `Sp_4(Z)`. That subgroup has property (T), hence finite
  abelianization, so the image would be finite. So every surjection `M' -> Z` is nonzero on Torelli.
- **Characters.** Composing with `exp(2 pi i theta .)`, `theta -> 0`, gives almost invariant vectors with
  no `K cap M'`-fixed vector.
- **Consequence.** `(Mod(S_2), I(S_2))` has no relative property (T). "Almost Torelli-scalar =>
  Torelli-scalar" rounding by a relative spectral gap is unavailable. The property (T) of `E_3` acts on the
  whole group, where the mark is central, not on Torelli.

## 6. Exact remaining gaps

- **G1.** `mod-s2-exact-representations-have-a-torelli-scalar-gap` (OPEN).
- **G2.** Is `sup_N l(N)` finite? This is a finite-group question about products of conjugates of a
  separating twist with exponent sum prime to 3. A bound settles the finite-image case.
- **G3.** Infinite-image exact representations beyond SU(2) WRT: other TQFTs, Jones representations of
  `B_6` descending to `Mod(S_2)`, and deformations in character varieties.
- **G4.** Flexible HS stability of `Mod(S_2)`. It is needed for (E3); its status is unknown here.
  `Mod(S_2)` contains `F_2 x F_2`.
- **Terminal.** A normalized-HS sector-rounding input for `E_3` or for `Sp_(2g)(Z)`. By
  `deligne-hs-metric-ladder-2026-09-13.md` Section 3 and Section 2 above, no weaker HS input is known.
