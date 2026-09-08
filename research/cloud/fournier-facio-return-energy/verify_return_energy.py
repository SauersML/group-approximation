#!/usr/bin/env python3
"""Exact checks for the return-energy inequality on cycle unitaries."""

from fractions import Fraction


def cycle_return_energy(d: int, n: int) -> Fraction:
    """E_n for any basis vector of the cyclic shift on d points."""
    return sum((n + 1 - k) for k in range(1, n + 1) if k % d == 0)


def check(d: int, n: int, expected_energy: int) -> None:
    energy = cycle_return_energy(d, n)
    assert energy == expected_energy
    denominator = Fraction(n + 1) + 2 * energy
    rank_lower_bound = Fraction((n + 1) ** 2, 1) / denominator
    assert Fraction(d) >= rank_lower_bound
    if d < n + 1:
        energy_lower_bound = Fraction((n + 1) * (n + 1 - d), 2 * d)
        assert energy >= energy_lower_bound
    print(
        f"PASS d={d}, N={n}: E={energy}, "
        f"rank lower bound={rank_lower_bound} <= {d}"
    )


if __name__ == "__main__":
    # Equality calibration: N=d-1 and the orbit is an orthonormal basis.
    check(d=5, n=4, expected_energy=0)
    # Independent non-equality cases, with genuine returns inside the window.
    check(d=3, n=4, expected_energy=2)
    check(d=2, n=5, expected_energy=6)
