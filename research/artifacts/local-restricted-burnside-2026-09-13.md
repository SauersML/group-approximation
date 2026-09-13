# Local restricted Burnside principle: reformulation, small-radius refutation, nilpotent case

Lane `solve-local-restricted-burnside`, 2026-09-13. Target: `LRB(m,N)` from
Attempt 5 of `hyperlinear-fg-bounded-exponent-groups-are-finite`.
- **`LRB(m,N)`:** there are `R_0` and `C` such that every finite `m`-generated
  group whose words of length `<= R_0` satisfy `h^N = 1` has order `<= C`.
- **Why it matters:** for odd `N >= n_1(F_m)` it would give a
  non-residually-finite hyperbolic group.

## Verdict

**Partial. Not decided at large odd exponents.**

## Nodes landed

| Node | Status | Content |
|---|---|---|
| `local-restricted-burnside-iff-partial-burnside-finite-quotients` (route `local-restricted-burnside-partial-burnside-proof`) | ESTABLISHED, unreviewed | see below |
| `partial-burnside-presentations-are-golod-shafarevich` (route `partial-burnside-golod-shafarevich-proof`) | ESTABLISHED, unreviewed | see below |
| `finite-nilpotent-groups-satisfy-local-restricted-burnside` (route `finite-nilpotent-local-restricted-burnside-proof`) | ESTABLISHED, unreviewed | see below |
| `golod-shafarevich-presentations-have-infinite-pro-p-completion` (route `golod-shafarevich-infinite-pro-p-citation`) | import | Ershov, arXiv:1206.0490, pinned below |
| `large-odd-exponent-local-restricted-burnside` | OPEN | the open instance; route `non-rf-hyperbolic-group-via-local-restricted-burnside` into `non-residually-finite-hyperbolic-group` |

**1. Reformulation** (`local-restricted-burnside-iff-partial-burnside-finite-quotients`).
- `LRB(m,N)` holds iff for some `R*` every finite quotient of
  `Π_{R*}(m,N) = F_m/⟨⟨h^N : |h| <= R*⟩⟩` has exponent dividing `N`.
- It holds when `B(m,N)` is finite.
- For odd `N >= n_1(F_m)` it makes **every** large Coulon stage `G_k`
  non-residually-finite.
- Conversely, residual finiteness of infinitely many stages refutes it.

**2. Small-radius refutation** (`partial-burnside-presentations-are-golod-shafarevich`).
- If a prime power `q | N` has `q >= 4R + 5`, the presentation of `Π_R(m,N)` is
  Golod–Shafarevich at `τ = 3/(2m)`.
- So there are unbounded finite `p`-groups satisfying the law on words of length
  `<= R`, and `LRB` fails at that radius.

**3. Nilpotent case** (`finite-nilpotent-groups-satisfy-local-restricted-burnside`).
- Above an ineffective radius, finite nilpotent groups satisfying the law on short
  words have exponent dividing `N`. The proof uses a Frattini argument in
  `ker(F_m -> R(m,q))` and Zelmanov.
- So large Coulon stages have finite pro-p completions for every `p`.
- `p`-groups cannot refute `LRB` at large radii.

## Implication check (directive step 1)

The Attempt 5 proof is correct. The node's route re-derives it in a stronger form:
- the kernels of `F_m -> G_k` increase with union `F_m^N`;
- so for `k >= k_0(R_0)`, `G_k` is a quotient of `Π_{R_0}`;
- its finite quotients are bounded by `C`;
- a finitely generated infinite group with bounded finite quotients has a
  finite-index finite residual, so it is not residually finite.

## Source pins

Ershov, *Golod–Shafarevich groups: a survey*, arXiv:1206.0490, `gssurvey_revised.tex`
(e-print fetched on MSI to `~/lrbp/`). Quoted verbatim in
`golod-shafarevich-infinite-pro-p-citation`:
- l.934–940, the degree function `D(f)=\deg(\iota(f)-1)`;
- l.944–951, the GS condition and GS groups (i)–(iii);
- l.954–960, the Remark that abstract presentations suffice (pro-p completion
  has the same presentation, citing Lubotzky Lemma 2.1);
- l.966–974, Theorem `GSinf`: "Golod-Shafarevich groups are infinite."

Line 1024, `D(f^{p^k})=D(f)^{p^k}`, reads as a typo for `p^k D(f)`. It was not used.

The route's lower bound `D(h^N) >= q` is proved directly from `(1+v)^q = 1+v^q`
in characteristic `p`.

**Not pinned:**
- Zelmanov: used only through the existing import `restricted-burnside-finiteness`.
- Burnside basis theorem, Schreier index formula, Malcev: standard.
- Breuillard–Gelander uniform Tits alternative: mentioned as a heuristic in
  Attempt 4 of the OPEN node, not used in any proof.

## Directive step 2: what was and was not done

- **(a) Computation.** `which gap` on MSI found no GAP, so no small-exponent
  coset enumerations ran. Two small-exponent facts hold without computation:
  - radius 1: `Π_1(m,N)` is the free product of `m` copies of `Z/N`, virtually
    free and infinite for `m >= 2`, so `LRB(1, m, N)` fails;
  - clause 4 of the reformulation: `LRB(m,N)` holds whenever `B(m,N)` is finite,
    e.g. `N = 2, 3, 4, 6`.

  Small exponents say nothing about odd `N >= n_1`.
- **(b) Zelmanov.** See Attempt 3 of `large-odd-exponent-local-restricted-burnside`.
  - The associated-Lie-ring identities use the law on deep elements of the lower
    central or Zassenhaus series, which are long words.
  - For `p`-groups, compactness gives a finite radius anyway (clause 1 of the
    nilpotent node).
  - For general finite groups, the passage to Sylow subgroups (Hall–Higman plus
    classification) does not localize. That passage is the break.

## Exact gap

Decide, for one odd `N >= n_1(F_m)` and `R` beyond `R_nil(m,N)`, whether the
partial Burnside group `Π_R(m,N)` has finite quotients of exponent not dividing
`N`. Such quotients must be non-nilpotent.
- **Yes for every `R`:** `LRB` fails.
- **No for some `R`:** a non-residually-finite hyperbolic group exists.

A positive answer to the residual finiteness question for hyperbolic groups
forces the first alternative.
