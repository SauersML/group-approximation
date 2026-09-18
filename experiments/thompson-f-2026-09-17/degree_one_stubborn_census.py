#!/usr/bin/env python3
"""Census of the first stubborn layer for degree-one sets S = {x_j : j in J}, J subset {0..5}, |J| >= 2.

For each J with max m, runs stubborn_core D (m + D + 1) J for D = 1, 2, ... (while the layer has
at most 400000 normal forms) and records the least D with a nonempty core and the core size.
Data only; see the claim thompson-f-generator-sets-admit-no-private-pivot-order.

usage: degree_one_stubborn_census.py path/to/stubborn_core   (prints JSON lines)
"""
import itertools, json, math, subprocess, sys

def main():
    binary = sys.argv[1]
    for m in range(1, 6):
        for r in range(2, m + 2):
            for J in itertools.combinations(range(m + 1), r):
                if J[-1] != m:
                    continue
                found = None
                for D in range(1, 9):
                    L = m + D + 1
                    if math.comb(L + D, D) > 400000:
                        break
                    out = json.loads(subprocess.run([binary, str(D), str(L), ";".join(map(str, J))],
                                                    capture_output=True, text=True).stdout)
                    if out["core"] > 0:
                        assert out["verified_stubborn"] is True
                        found = {"D": D, "L": L, "core": out["core"]}
                        break
                print(json.dumps({"J": list(J), "first_core": found, "searched_to_D": D}), flush=True)

if __name__ == "__main__":
    main()
