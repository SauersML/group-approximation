"""Numerical checks for the proved corner-dilation budget; not a group witness.

Run: python experiments/corner_dilation_budget_check.py
Requires NumPy and SciPy. The mathematical proof is in
research/artifacts/sl3-corner-descent-dilation-budget-2026-09-05.md.
"""

import json
import math

import numpy as np
from scipy.integrate import quad


def unitary(r, rng):
    z = rng.normal(size=(r, r)) + 1j * rng.normal(size=(r, r))
    return np.linalg.qr(z)[0]


def curve(beta):
    length = math.pi * (1 - beta) / 2
    return 2 / math.pi * (
        1.5 * length - 2 * math.sin(length) + math.sin(2 * length) / 4
    )


def main():
    rng = np.random.default_rng(20260905)
    max_unitarity_error = max_attainment_error = 0.0
    min_random_slack = float("inf")
    cases = 0
    for r in [1, 2, 3, 5, 8]:
        spectra = [np.zeros(r), np.ones(r), np.linspace(0, 1, r), rng.random(r)]
        for spectrum in spectra:
            a = np.sort(spectrum)[::-1]
            left, right = unitary(r, rng), unitary(r, rng)
            source = left @ np.diag(a) @ right.conj().T
            for k in range(r + 1):
                predicted = float(np.sum((1 - a[: r - k]) ** 2) / r)
                dilation = np.eye(r + k, dtype=complex)
                for j, i in enumerate(range(r - k, r)):
                    b = math.sqrt(max(0.0, 1 - a[i] ** 2))
                    dilation[i, i] = dilation[r + j, r + j] = a[i]
                    dilation[i, r + j], dilation[r + j, i] = -b, b
                dl, dr = np.eye(r + k, dtype=complex), np.eye(r + k, dtype=complex)
                dl[:r, :r], dr[:r, :r] = left, right.conj().T
                dilation = dl @ dilation @ dr
                defect = np.linalg.norm(dilation.conj().T @ dilation - np.eye(r + k))
                actual = float(np.linalg.norm(source - dilation[:r, :r]) ** 2 / r)
                competitor = unitary(r + k, rng)[:r, :r]
                slack = float(np.linalg.norm(source - competitor) ** 2 / r - predicted)
                max_unitarity_error = max(max_unitarity_error, float(defect))
                max_attainment_error = max(max_attainment_error, abs(actual - predicted))
                min_random_slack = min(min_random_slack, slack)
                assert defect < 1e-12 and abs(actual - predicted) < 1e-12
                assert slack > -1e-12
                cases += 1

    r = 32768
    angles = (np.arange(r) + 0.5) * math.pi / (2 * r)
    singular_values = np.cos(angles)  # Decreasing; limiting |A| law.
    curve_rows = []
    max_quadrature_error = 0.0
    for beta in [0, 0.25, 0.5, 0.75, 0.875, 1]:
        k = round(beta * r)
        empirical = float(np.sum((1 - singular_values[: r - k]) ** 2) / r)
        closed = curve(beta)
        integrated = 2 / math.pi * quad(
            lambda t: (1 - math.cos(t)) ** 2, 0, math.pi * (1 - beta) / 2
        )[0]
        max_quadrature_error = max(max_quadrature_error, abs(closed - integrated))
        assert abs(closed - integrated) < 1e-12
        assert abs(empirical - closed) < 1e-8
        curve_rows.append({"padding_ratio": beta, "squared_error": closed,
                           "finite_spectrum_error": abs(empirical - closed)})

    print(json.dumps({"seed": 20260905, "finite_dilation_cases": cases,
                      "max_unitarity_error": max_unitarity_error,
                      "max_attainment_error": max_attainment_error,
                      "minimum_random_competitor_slack": min_random_slack,
                      "max_quadrature_error": max_quadrature_error,
                      "arcsine_spectrum_size": r, "curve": curve_rows}, indent=2))


if __name__ == "__main__":
    main()
