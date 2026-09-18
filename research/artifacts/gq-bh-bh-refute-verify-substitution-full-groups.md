# Adversarial check: substitution-subshift full groups and quadratic IET groups satisfy Boone–Higman (bh-refute, 2026-09-18)

This is an independent red-team verification of three ESTABLISHED lane proofs by bh-free-03:
`stationary-vershik-maps-generate-contracting-rsgs` (with its proof),
`substitution-subshift-full-groups-satisfy-boone-higman` (with its proof), and
`quadratic-rotation-iet-groups-satisfy-boone-higman` (with its proof).
Verdict: **PASS, conditional on the cited imports**, which were not re-read here. Those are:
- the BBMZ RSG results imported through `contracting-rsgs-embed-in-fp-simple-groups`: the composition
  lemma, Prop. `NucleusHasProperties`, Thm `RSGCharacterization` and Prop. `contr_to_simple`;
- DHS Theorem 1 (stationary Bratteli–Vershik models of substitution subshifts);
- substitutivity of Sturmian shifts of quadratic slope.

No gap was found in the lane-proved steps.

If correct, this is a notable result: it places Juschenko–Monod-type f.g. simple amenable groups
`[[S]]'` for substitution subshifts inside finitely presented simple groups.

## The contracting-RSG step (the new mathematics)

- **Local actions of `T` (Step 2).** Checked on the maximal cones `M(v,k)`.
  - Constant first letter `l` and last letter `r` make the reset path `P_k = r_l (l,1)^{k-2}` independent
    of the tail.
  - `T(M(v,k) ω) = P_k τ_v(ω)` with `τ_v` independent of `k`, so `T` has finitely many local actions.
  - The recursion when `ω_1` is maximal forces `v = r` and just increases `k`. This is correct.
- **No stacking of singular germs (Steps 4–5).** This is the crux, and it holds.
  - Canonical similarities replace prefixes, so they preserve tails. `x_min` has tail `(l,1)^∞` and
    `x_max` has tail `(r,L_r)^∞`. These are distinct because `L_r >= 2`, so no similarity joins them (4(a)).
  - When `T` is followed by a similarity `c` fixing `x_min` and then `T^{-1}`, the depth shift of `c`
    transports to `x_max`. I checked `T^{-1} c T (x_max[1..m] ω) = x_max[1..m+d] ω` directly from the
    Vershik rule: reset to minimal, shift, then decrement back to maximal. It uses that `min^a` and
    `min^{a+d}` both end at `l`, and `max^m`, `max^{m+d}` both end at `r`.
  - The induction on word length covers all cases:
    - right multiplication by a similarity;
    - `T` at `x ≠ x_max` (a similarity);
    - `T` at `x_max` with `x_min ∉ S_g`, giving the normal form with `c_2 = id`;
    - `T` at `x_max` with `x_min ∈ S_g`, where `ε = 1` is excluded by 4(a) and `ε = −1` cancels by 4(b);
    - the symmetric cases for `T^{-1}`.

    Every germ of `G_0` is a similarity or `c_1 T^{±1} c_2`.
- **Finite nucleus (Step 6).** Local actions at deep cones of `c_1 T^ε c_2` are those of `T^ε`, since
  canonical similarities have identity local actions. So `Nuc_{G_0} ⊆ {id} ∪ Nuc_T ∪ Nuc_{T^{-1}}`.
  Checked.

## The full-closure step

`[[T]] <= G_N` holds because an element of `[[T]]` is, near each point, equal to some `T^{n}` in `G_0`. Its
local actions at all sufficiently deep cones are therefore those of the finitely many `T^{n_i}`, all
inside `N = Nuc_{G_0}`. The only input used is that membership in `G_N` is decided by the eventual local
actions, which is BBMZ's characterization as imported.

## The IET step

Breakpoints in `Λ = Z + αZ` are exactly the orbit points `nα mod 1`. So after doubling that orbit, the
pieces are clopen, and a translation `t ≡ nα (mod 1)` is `R_α^n` on its piece. Hence
`IET(Λ) <= [[R_α]]` injectively. Checked. The substitutive input for quadratic `α` is standard, and it is
the node's stated trust surface.

## Attacks tried (all failed)

- **Two singular germs meeting through `V`.** Impossible, since they have different tails.
- **Nucleus growth from the reset path.** It is independent of depth, by the constant-letter hypotheses.
  Without constant first and last letters, `P_k` would depend on the tail, and the argument would really
  need the DHS proper-ordering normalization, which the proof invokes via
  `substitution-subshifts-have-stationary-bv-models`.
- **Full closure admitting non-rational maps.** Elements of `[[T]]` are piecewise powers of `T`, hence
  rational.

## Priority

An arXiv API search on 2026-09-18 for "topological full group" with "finitely presented", "rational" or
"Boone" returned 7 entries. None states that full groups of minimal or substitution subshifts embed in
finitely presented simple groups. Matui 1210.5800 concerns one-sided SFTs. The node's "no priority
claimed" stands; the search is bounded.
