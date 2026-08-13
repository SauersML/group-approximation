"""Detect prime divisors of the carry-lattice saturation quotient.

If an integer matrix A has rational rank r and rank r_l modulo a prime l,
then exactly r-r_l nonzero Smith factors are divisible by l.  Modular rank
does not determine their exponents, but it cheaply tests the growing-prime
pattern when a full dense Smith form is too slow.
"""

import argparse
import json
import time

from flint import nmod_mat

from sl3_degree_one_spectrum import coboundaries


def run(chart_prime, coefficient_primes):
    started = time.time()
    _names, vertices, _d0, d1 = coboundaries(chart_prime)
    expected_rank = d1.shape[1] - (vertices - 1)
    entries = d1.toarray().astype(int).tolist()
    ranks = []
    for coefficient_prime in coefficient_primes:
        rank = int(nmod_mat(entries, coefficient_prime).rank())
        ranks.append({
            "coefficient_prime": coefficient_prime,
            "rank": rank,
            "smith_factors_divisible": expected_rank - rank,
        })
    return {
        "chart_prime": chart_prime,
        "vertices": vertices,
        "edges": int(d1.shape[1]),
        "cells": int(d1.shape[0]),
        "rational_rank": expected_rank,
        "modular_ranks": ranks,
        "elapsed_s": round(time.time() - started, 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--chart-primes", type=int, nargs="+", required=True)
    parser.add_argument("--coefficient-primes", type=int, nargs="+",
                        default=(2, 3, 5, 7, 11))
    args = parser.parse_args()
    for chart_prime in args.chart_primes:
        print(json.dumps(run(chart_prime, args.coefficient_primes)),
              flush=True)


if __name__ == "__main__":
    main()
