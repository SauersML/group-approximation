# Referee report (gq-referee-a, proof-gap lens): renormalization return times tend to zero adically

**Reviewed:** `renormalization-return-times-tend-to-zero-adically` and its `-proof` (lane gq-nv-obstruct), read on
origin/main (db7acc3f9). No referee had reviewed it before.

**Verdict: PASS.** Items 1–3 hold, and I found no gap. N1 corrects the direction of one implication in the
tape-coding sentence of item 2; the linear-radius conclusion survives with different constants. Item 1 is cited
from `renormalizable-thompson-elements-are-odometer-codes`. The MSI return data is a calibration, not an input.

## Checks
- **Item 1.** `π(x) = digit(x) + m·π(Sx)`. At `digit(x) = m−1`, `Tx ∈ T^m A = A`, and
  `S(Tx) = φ(T^m T^(−(m−1))x) = Tφ(T^(−(m−1))x) = T(Sx)`. That is the carry, so `π∘T = π + 1`. This agrees with the
  cited item.
- **Item 2, the base case.** Every depth-`D` brick lies in a single `T^iA`, because the `T^iA` are unions of bricks
  of depth at most `D` and bricks nest. So `π mod m = digit` is constant on depth-`D` bricks. ✓
- **Item 2, the step.** Take `x` in a depth-`(D + jP)` brick `Br`.
  - `Br` lies in one depth-`D` brick of some `T^iA`, so `digit` is constant on it, and `S = φT^(−i)` is canonical there.
  - By the definition of `P`, the depth-`(D + (j−1)P)` brick of `Sx` is determined by `Br`. So by induction
    `π(Sx) mod m^j` is constant on `Br`.
  - Hence `π mod m^(j+1) = digit + m·(π∘S mod m^j)` is constant on `Br`. The exponent matches
    `D + ((j+1)−1)P`. ✓
- **Item 3.**
  - `π∘T^n = π + n` for all `n ∈ Z`, and `π` is continuous. So `π(y) + n_i → π(y)` in `Z_m`.
  - For an integer `n`, `n ∈ m^jZ_m ⟺ m^j | n`. So `m^j ∤ n_i` for all `i` keeps `n_i` outside a neighbourhood of 0,
    which is a contradiction. ✓

## Nit
- **N1 (item 2, the tape-coding sentence).** The proof says that a depth-`d` brick fixes the state and the cells
  within `(d − c_0)/c_1` of the head. That is the direction "brick determines cells".
  - The radius form needs the converse: the state and the cells within some radius `r(d)` determine the depth-`d`
    brick.
  - That converse holds with `r(d) ≤ d/c_min + O(1)`, because every cell code has length at least `c_min ≥ 1`.
  - So `π mod m^j` is a function of the state and the cells within `a + b·j`, with `b` about `P/c_min` rather than
    `P/c_1`.
  - The statement "for constants `a, b`" is unaffected. Fix the sentence and the constants.
