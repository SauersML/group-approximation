# Finite complete rewriting system search for the Basilica and Grigorchuk HNN extensions (2026-09-17, sw-093)

Goal: a finite complete rewriting system (FCRS) certifies `FP_∞`. With finite presentation, that
gives `F_∞` for an amenable, non-elementary-amenable group (Zaremsky 1.12).

## Files

- **`kb.cpp`**: the Knuth–Bendix completer. Build with `g++ -O2 -o kb kb.cpp`.
  - Input on stdin: letter ranks (lowest first, where the inverse of `x` is `swapcase(x)`), then
    `wreath|shortlex`, then `max_rules max_len`, then relators.
  - Equations are processed shortest first. Rules are interreduced, and equations with a side
    longer than `max_len` are deferred.
  - If completion finishes, it re-checks all critical pairs and all deferred equations
    independently before printing `COMPLETE`.
- **`pres.py`**: the presentations. Usage: `python3 pres.py <name> <order> <ordering> <max_rules> <max_len>`.
  - `bs12`: `⟨a, t | t a t^-1 = a^2⟩`.
  - `basilicaHNN`: `⟨a, t | t^-2 a t^2 = a^2, [a, a^b], b = t a t^-1⟩`, with `σ: a ↦ b^2, b ↦ a`.
  - `grigorchukHNN`: `⟨a,b,c,d,t | a^2, b^2, c^2, d^2, bcd, t^-1 x t = σ(x), (ad)^4, (adacac)^4⟩`,
    with `σ: a ↦ aca, b ↦ d, c ↦ b, d ↦ c`.
  - `thompsonF`: used for calibration only.
- **`basilica_sigma_check.py`, `grigorchuk_sigma_check.py`**: check that `σ^k` of the relators is
  trivial on level 14 of the binary tree.
  - Basilica, `σ: a ↦ b^2, b ↦ a`: trivial for `k = 1..4`.
  - The substitution `a ↦ b, b ↦ a^2` fails at `k = 1` and `k = 3`, so it is not an endomorphism.
    This caught a convention slip during the session.
  - Grigorchuk: Lysenok's `σ` is trivial for `k = 1..3`; a control substitution fails.
- **`runall.sh`**: the batch. Each run uses 3000 active rules, `max_len` 30 and a 300 s timeout.
- **`out/`**: raw outputs. `*.txt` holds the status line and the active rules at overflow; `*.log`
  holds progress.

## Results

| group | rank order (low→high) | ordering | outcome | active rules | lhs length at last report | deferred |
|---|---|---|---|---|---|---|
| BS(1,2) | a A t T | wreath | **COMPLETE**, 8 rules, verified | 8 | – | 0 |
| BS(1,2) | t T a A | wreath | timeout 120 s | 1041 | 27 | 12095 |
| BS(1,2) | T t A a | wreath | timeout 120 s | 1045 | 26 | 6849 |
| BS(1,2) | a A t T | shortlex | timeout 120 s, no report | – | – | – |
| Basilica HNN | a A t T | wreath | overflow | 3001 | 21 | 3981 |
| Basilica HNN | A a t T | wreath | overflow | 3001 | 24 | 2574 |
| Basilica HNN | t T a A | wreath | timeout 300 s | 2673 | 18 | 13221 |
| Basilica HNN | a A t T | shortlex | overflow | 3001 | 22 | 190 |
| Grigorchuk HNN | a A b B c C d D t T | wreath | timeout 300 s | 1153 | 21 | 40494 |
| Grigorchuk HNN | t T a A b B c C d D | wreath | timeout 300 s | 2773 | 21 | 13609 |
| Grigorchuk HNN | a A b B c C d D t T | shortlex | overflow | 3001 | 20 | 0 |
| Thompson F | y Y x X | wreath | growth past 1500 rules in 30 s (whether F has an FCRS is open) | – | – | – |

The BS(1,2) complete system is `Tt→1, tT→1, Aa→1, aA→1, aT→Taa, aat→ta, At→atA, AT→TAA`.

## What this rules out

- **Base-first wreath ordering for Grigorchuk.** The run on `a A b B c C d D t T` can never
  succeed, for a structural reason proved in
  `research/grigorchuk-hnn-has-no-base-first-wreath-rewriting-system-proof.md`. Restricting the
  system to the eight base letters would give a finite presentation of `𝔊`. The overflow here is
  the calibration of that theorem.
- **All other runs.** They show only that this completion procedure reaches no FCRS within 3000
  rules, length 30 and 300 s. That is not a proof of non-existence. Left-hand sides keep growing
  (18–27 letters) with no plateau.
- **BS(1,2) calibration.** Even `BS(1,2)` fails to complete under t-lowest wreath and shortlex
  within the same bounds. The orderings that survive the obstruction are therefore computationally
  hostile already for the simplest ascending HNN extension. Only t-highest wreath works for
  `BS(1,2)`, and for `𝔊^` that ordering is exactly the one the theorem kills.
