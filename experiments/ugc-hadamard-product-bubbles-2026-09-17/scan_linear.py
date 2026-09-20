"""Scan dead-zone linear profiles g(w) = clip((w - theta)/(1 - theta)) in the limit model."""
import sys
import numpy as np
from limit_product import Profile, chi_table, config_prices, boolean_configs, fractional_configs


def worst(prof, mmax=4, grid=(1, 0.5, 0, -0.5, -1), mfrac=2):
    best = (-1, None)
    for m in range(1, mmax + 1):
        C = chi_table(m)
        for f in boolean_configs(m):
            p = max(config_prices(f, C, prof))
            if p > best[0]:
                best = (p, ("bool", m, tuple(f)))
    for m in range(1, mfrac + 1):
        C = chi_table(m)
        for f in fractional_configs(m, grid):
            if np.allclose(C @ f, 0):
                continue
            p = max(config_prices(f, C, prof))
            if p > best[0]:
                best = (p, ("frac", m, tuple(f)))
    return best


if __name__ == "__main__":
    # sanity: single pin, linear theta = 0 -> 3/2 everywhere
    prof = Profile([0, 1], [0, 1])
    C = chi_table(1)
    for c in (0.2, 0.5, 0.9):
        print("single pin c=%.1f" % c, config_prices(np.array([c, -c]), C, prof))
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for th in (0.0, 0.1, 0.2, 0.25, 0.3, 1 / 3, 0.4, 0.5):
        prof = Profile([0, th, 1], [0, 0, 1]) if th > 0 else Profile([0, 1], [0, 1])
        p, cfg = worst(prof, mmax)
        print(f"theta={th:.3f}: worst {p:.4f} at {cfg}")
