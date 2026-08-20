#!/usr/bin/env python3
"""Replay the exact algebra behind the renormalization-stable-letter audit.

The checks are deliberately finite and symbolic.  They do not assert that a
twisted Clifford substitution extends to an endomorphism of the proposed
finitely presented Thompson--Clifford group.
"""

from __future__ import annotations

from itertools import product


def multiply_laurent_mod(
    left: dict[int, int], right: dict[int, int], modulus: int
) -> dict[int, int]:
    out: dict[int, int] = {}
    for i, a in left.items():
        for j, b in right.items():
            out[i + j] = (out.get(i + j, 0) + a * b) % modulus
    return {degree: coefficient for degree, coefficient in out.items() if coefficient}


def verify_z4_ghost_doubling() -> None:
    phi = {0: 2, 1: 1}  # 2I + S
    square = multiply_laurent_mod(phi, phi, 4)
    assert square == {2: 1}
    print("Z4: (2I+S)^2 = S^2")


def led_rappier_lift(y: tuple[int, ...], seed: int) -> tuple[int, ...]:
    """Solve y_i=x_i+x_(i-1) on an interval from one boundary seed."""
    x = [seed]
    for bit in y:
        x.append(bit ^ x[-1])
    return tuple(x)


def verify_ledrappier_window(width: int = 9) -> None:
    for y in product((0, 1), repeat=width):
        lifts = [led_rappier_lift(y, seed) for seed in (0, 1)]
        assert lifts[0] != lifts[1]
        for x in lifts:
            assert tuple(x[i + 1] ^ x[i] for i in range(width)) == y
        assert tuple(a ^ b for a, b in zip(*lifts)) == (1,) * (width + 1)
    print(f"F2: every width-{width} target has two lifts differing by the constant kernel")


def triple_square_exponent(square_exponents: tuple[int, int, int]) -> int:
    """J-exponent of (abc)^2 when every distinct pair anticommutes by J."""
    return (sum(square_exponents) + 3) % 2


def verify_clifford_square_bookkeeping() -> None:
    involutive_factors = triple_square_exponent((0, 0, 0))
    order_four_factors = triple_square_exponent((1, 1, 1))
    assert involutive_factors == 1
    assert order_four_factors == 0
    print("Clifford: three involutive pairwise-ant commuting factors square to J")
    print("Clifford: three J-square pairwise-ant commuting factors square to 1")
    print(
        "compatibility law: source square exponent = "
        "sum(factor square exponents)+1 (mod 2)"
    )


if __name__ == "__main__":
    verify_z4_ghost_doubling()
    verify_ledrappier_window()
    verify_clifford_square_bookkeeping()
