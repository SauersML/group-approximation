# Fibred quotients for single-edge H_4 bottom triples (w5-042)

These scripts support `research/h4-case1-pure-normal-form-and-fibred-obstruction.md`.

Run them with `python3 fibred.py > fibred.log` and `python3 augment.py | sort | uniq -c > augment.log`. Each
takes a few seconds and needs only numpy.

- `fibred.py`
  - Builds the `H_3` and `H_4` root systems from the Gram matrix.
  - Takes `x = ω_1` and `y = ω_n`, the fixed lines of `W_X` and `W_Y`.
  - Checks that `ℓ_x` is modular in `𝒜_x ∪ 𝒜_y`: every collision normal of two walls of `𝒜_y∖𝒜_z` is an
    `𝒜_z` root.
  - Counts the flats `w ∩ w'` with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z`, by type.
- `augment.py`: for each non-commuting such flat `V`, forms `ℬ_V = 𝒜_x ∪ 𝒜_y ∪ 𝒜_V`, tests whether `ℓ_x` is
  still modular, and counts the collision walls outside `𝒜_z`.

Results:
- `H_4`, `|𝒜_x ∪ 𝒜_y| = 18`. The fibration is `ℂ` minus 3 points over `M(H_3)`.
- The 9 `A_2` flats all give 19 walls, with `ℓ_x` modular, 4 fibre points and 3 collision walls outside `𝒜_z`.
- 3 of the 15 `I_2(5)` flats give 21 walls with `ℓ_x` modular.
- `H_3` calibration: 2 `I_2(5)` flats give 10-wall fibred arrangements, the size of Huang's auxiliary
  arrangement I.

Tolerance is `1e-9` on unit-normalised roots; all roots have norm 1 and the entries lie in `ℚ(√5)`.
