#!/usr/bin/env python3
"""Replay the exact verification for every stored witness, with no random search.

For each row of ratio_search_n{2,3,4,6}.json, rebuild U, W exactly over Q(i) from the stored
integer Cayley parameters (via ratio_search.verify), and check with exact rational arithmetic
that e(c) >= B^2 max(e(R1), e(R2)) for the claimed bound B (a terminating decimal).

Single-threaded; run with `timeout 600`.
"""
import json
import sys
from fractions import Fraction as Q

import numpy as np

sys.path.insert(0, ".")
from ratio_search import verify  # noqa: E402

CLAIMS = {2: Q("2.4141"), 3: Q("2.4141"), 4: Q("3.2286"), 6: Q("3.2221")}

ok = True
for n in (2, 3, 4, 6):
    d = json.load(open(f"ratio_search_n{n}.json"))
    for row in d["rows"]:
        den = row["cayley_params_rounded_den"]
        p = np.array(row["params"], dtype=float) / den
        ec, e1, e2 = verify(p, n, den)
        emax = max(e1, e2)
        B = CLAIMS[n]
        holds = ec >= B * B * emax
        ok = ok and holds
        print(json.dumps({"n": n, "tau": row["tau"], "e_c": float(ec), "e_R1": float(e1), "e_R2": float(e2),
                          "claimed_lower_bound": str(B), "exact_check_holds": bool(holds),
                          "e_c_denominator_digits": len(str(ec.denominator))}))
print("ALL_EXACT_CHECKS_HOLD" if ok else "SOME_CHECK_FAILED")
