# KBMAG completion search for the Basilica HNN extension (Kourovka 21.140 crux), 2026-09-19

Lane bh-free-58. This is the rewriting route to `basilica-hnn-extension-is-fp-infinity`.
- **Why it matters.** A finite complete rewriting system for `B~` would give `FP_∞`, by
  Anick/Squier/Brown collapsing. With finite presentation that is `F_∞`, and `B~` would answer
  Kourovka 21.140.
- **The complementary result.** Σ-theory cannot give `FP_3` here (crux node, Σ bullet, commit
  e8e06719b).
- **Relation to earlier work.** This repeats and extends the custom-completer search
  `experiments/hnn-rewriting-2026-09-17` (sw-093) with an established tool, KBMAG.

## Setup (MSI acn112, standing small-compute envelope)

- **Placement.** Every run was `taskset -c 30,31 nice -n 19 timeout <≤900>`, one at a time, with
  output under `/projects/standard/hsiehph/sauer354/bh-free-58/kb/`. Nothing ran locally. Total
  kbprog time was about 13 minutes.
- **The tool.** KBMAG (D. Holt; GAP package source `github.com/gap-packages/kbmag`). There is no GAP
  on MSI, so `kbprog` was compiled directly:
  `gcc -O2 -w -Istandalone/lib -o bin/kbprog standalone/src/kbprog.c standalone/lib/*.c -lm`.
- **The call.** `kbprog -v -me 200000 -t 500 <file>`, i.e. an equation cap of 200 000.
- **Run script** (`run.sh <name> <seconds>`). It copies `inputs/<name>` into `runs/`, runs the
  pinned `kbprog`, and appends `RUN <name> rc=<rc> secs=<s>` to the log. Exit code `124` means
  timeout, and exit code `2` with "Maximum number of equations exceeded" means cap.
- **Summary script** (`summary.sh <name>`). An awk pass over `<name>.kbprog` reports the equation
  count, the median and maximum LHS length, and the head of the longest LHS.

## Inputs

- **Presentation.** `B~ = ⟨a, t | t^-2 a t^2 = a^2, [a, a^b] = 1⟩` with `b = t a t^-1`. The
  inverses are `A = a^-1` and `T = t^-1`.
  - The relator `[a, a^b] = a^-1 (a^b)^-1 a (a^b)`, with `a^b = b^-1 a b`, expands to
    `A*t*A*T*A*t*a*T*a*t*A*T*a*t*a*T`.
  - Equations: `[T*T*a*t*t, a^2]` and `[A*t*A*T*A*t*a*T*a*t*A*T*a*t*a*T, IdWord]`.
- **Orderings.** `shortlex`, `recursive` and `rt_recursive`, each with generator order `[a,A,t,T]`
  or `[t,T,a,A]`. Also `wreathprod` with `[a,A,t,T]` and levels `[1,1,2,2]`, so `t` dominates.
- **Planted positive (calibration).** `BS(1,2) = ⟨a, t | t a t^-1 = a^2⟩` under `recursive` and
  `rt_recursive`, `[a,A,t,T]`.

## Results

| input | ordering (generator order) | outcome | equations | LHS length profile |
|---|---|---|---|---|
| BS(1,2) | recursive (a A t T) | **confluent**, 0 s | 8 | matches the known 8-rule system |
| BS(1,2) | rt_recursive (a A t T) | **complete**, 0 s | 8 | exit 0 |
| B~ | shortlex (a A t T) | cap after 6 s | 198 669 | median 19, max 34; bell-shaped |
| B~ | shortlex (t T a A) | cap after 8 s | 198 092 | median 19, max 31; bell-shaped |
| B~ | recursive (a A t T), t highest | cap after 69 s | 191 180 | median 21, max 1965; the longest LHS contains `A^1943` |
| B~ | recursive (t T a A), t lowest | timeout 170 s | 160 205 | total LHS 10.6 M, 3.8 M states |
| B~ | wreathprod, t over a | timeout 170 s | 19 440 | mean LHS ≈ 475, 3.8 M states |
| B~ | rt_recursive (a A t T) | timeout 170 s | 12 982 | mean LHS ≈ 287, 1.6 M states |
| B~ | rt_recursive (t T a A) | timeout 170 s | 69 790 | mean LHS ≈ 77, 1.9 M states |

## How the orderings diverge

1. **Length-first orders** (shortlex, both generator orders).
   - The rules pile up at moderate lengths: a bell-shaped LHS histogram with median 19 and nearly
     all rules at length ≤ 34. The cap of 200 000 is hit within seconds.
   - This is the signature of rule counts growing exponentially with length, not of a few
     infinite regular families.
2. **Recursive, t highest** (the order that completes `BS(1,2)`).
   - The system grows *infinite regular-looking families*. Rules containing `A^n` for unbounded
     `n` appear; the longest has `A^1943`.
   - The LHS-length histogram has a long tail with period-4 repeating counts, from about 400 to
     about 1960.
   - The ascending relation `t^-2 a t^2 = a^2` pushes powers of `a` through `t`-words, as in
     `BS(1,2)`, but the commutator relation stops the families from collapsing.
3. **t-lowest and mixed orders** (recursive with t lowest, wreathprod, both rt_recursive).
   - The rules get very long (mean LHS 77–475) and the reduction automaton reaches 1.6–3.8 M states
     before the timeout.
   - This is the same qualitative picture that sw-093 found for t-lowest wreath with the custom
     completer.

**What was not done.** No run was simply extended, as instructed. No positive output occurred, so
no independent confluence check was needed.

## Interpretation (heuristic)

- **Not a proof of non-existence.** These runs show only that KBMAG finds no finite complete
  system under seven orderings within the caps. Every run was calibrated: both BS(1,2) runs complete
  at once.
- **The divergence pattern points to a structural obstruction.**
  - Orders where `t` dominates must absorb the BS-type `a`-power families, and the Basilica
    commutator relation keeps generating new ones.
  - Length-first orders face the non-automatic-looking growth of the Basilica relation module.
  - This mirrors Grigorchuk's case, where base-first wreath orders provably cannot succeed
    (`grigorchuk-hnn-has-no-base-first-wreath-rewriting-system`). There the base group is
    generated by base letters. That argument does not transfer to `B~`, because `a` alone does not
    generate the base `B = ⟨a, tat^-1⟩`.
- **Status of the crux.** The rewriting route to `FP_∞` for `B~` is not closed, but it is not
  promising: seven orderings, two tools, no plateau. With Σ-invisibility (e8e06719b) and the absence
  of a finitely presented ascending base (83b85aaed), the positive direction of the 21.140 crux has
  no working method.

## Lesson for general BH

**Branch-group finitizations resist every finite-rewriting ordering in the same two ways.**
- Dominating the stable letter produces unbounded BS-type power families.
- Length-first ordering produces exponential rule growth from the branch relations.

**For hosts.** Certifying `F_∞` of such self-similar HNN hosts will need geometric (Brown/Stein–Farley)
complexes adapted to the branch structure, not word combinatorics. That is the same conclusion as
for germ and self-similar hosts elsewhere on the master route.
