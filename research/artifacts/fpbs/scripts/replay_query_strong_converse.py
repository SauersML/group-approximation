#!/usr/bin/env python3
"""Exact capped-query likelihood and binomial testing bounds. Run on MSI."""

from collections import defaultdict
from fractions import Fraction as F
from math import comb
import itertools
import json
import time

from replay_exploration_information import explore


def binomial_testing_bound(m, c, q, budget):
    """Maximize q-mass at prescribed c-mass, allowing boundary randomization."""
    remaining, total = budget, F(0)
    for opened in range(m, -1, -1):
        pc = comb(m, opened)*c**opened*(1-c)**(m-opened)
        pq = comb(m, opened)*q**opened*(1-q)**(m-opened)
        used = min(remaining, pc)
        total += used*pq/pc
        remaining -= used
    assert remaining == 0
    return total


def main():
    started = time.monotonic()
    graphs = [(3, [(0, 1), (1, 2)]),
              (3, [(0, 1), (1, 2), (0, 2)]),
              (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
              (4, list(itertools.combinations(range(4), 2)))]
    cases = configurations = prefixes = 0
    examples = []
    for vertices, edges in graphs:
        for source, target in itertools.combinations(range(vertices), 2):
            for beta in (0, 1, 2):
                runs = []
                for bits in itertools.product((0, 1), repeat=len(edges)):
                    success, trace = explore(vertices, edges, bits, source, target,
                                             direction=beta)
                    runs.append((sum(bits), success, trace))
                    configurations += 1
                for c, q in ((F(1, 3), F(1, 2)), (F(1, 2), F(3, 4))):
                    factor = q*q/c+(1-q)**2/(1-c)
                    assert factor == 1+(q-c)**2/(c*(1-c))
                    for cap in range(len(edges)+1):
                        laws = {p: defaultdict(F) for p in (c, q)}
                        success_mass = {c: F(0), q: F(0)}
                        for opened, success, trace in runs:
                            for p in (c, q):
                                mass = p**opened*(1-p)**(len(edges)-opened)
                                laws[p][trace[:cap]] += mass
                                if success and len(trace) <= cap:
                                    success_mass[p] += mass
                        moment = normalized_moment = F(0)
                        for prefix, pc in laws[c].items():
                            used = len(prefix)
                            opened = sum(bit for _, bit in prefix)
                            likelihood = (q/c)**opened*((1-q)/(1-c))**(used-opened)
                            assert pc == c**opened*(1-c)**(used-opened)
                            assert laws[q][prefix] == pc*likelihood
                            moment += pc*likelihood**2
                            normalized_moment += pc*likelihood**2/factor**used
                        assert normalized_moment == 1
                        assert moment <= factor**cap
                        a, b = success_mass[c], success_mass[q]
                        optimal = binomial_testing_bound(cap, c, q, a)
                        assert b <= optimal
                        assert b*b <= a*factor**cap
                        assert optimal*optimal <= a*factor**cap
                        assert binomial_testing_bound(cap, c, q, F(0)) == 0
                        assert binomial_testing_bound(cap, c, q, F(1)) == 1
                        if vertices == 4 and len(edges) == 6 and (source, target) == (0, 3) and beta == 2 and c == F(1, 3):
                            examples.append({"cap": cap, "success_c": str(a),
                                             "success_q": str(b),
                                             "binomial_optimum": str(optimal),
                                             "second_moment": str(moment),
                                             "second_moment_cap": str(factor**cap)})
                        cases += 1
                        prefixes += len(laws[c])
    print(json.dumps({"status": "passed", "arithmetic": "exact rational",
                      "scope": "Finite adaptive prefixes and exact testing bounds; not a proof of critical spectral decay or universal nonuniqueness",
                      "cap_cases": cases, "graph_configurations": configurations,
                      "prefixes": prefixes, "complete_graph_examples": examples,
                      "elapsed_seconds": round(time.monotonic()-started, 3)}, indent=2))


if __name__ == '__main__':
    main()
