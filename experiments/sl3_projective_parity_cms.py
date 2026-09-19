"""Minimum-support Wall fillings using CryptoMiniSat's native XOR clauses."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pycryptosat import Solver
from pysat.card import CardEnc, EncType

from sl3_projective_parity_milp import (
    linear_seed,
    read_binary_boundary,
    verify_selected,
)


def bounded_solve(
    columns: list[set[int]],
    source_rank: int,
    target: set[int],
    bound: int,
    time_limit: float,
):
    solver = Solver(verbose=0, time_limit=time_limit, threads=1)
    for coordinate, sources in enumerate(columns):
        variables = [source + 1 for source in sorted(sources)]
        parity = coordinate in target
        if not variables:
            if parity:
                return False, None
            continue
        solver.add_xor_clause(variables, parity)
    cardinality = CardEnc.atmost(
        lits=list(range(1, source_rank + 1)),
        bound=bound,
        top_id=source_rank,
        encoding=EncType.seqcounter,
    )
    for clause in cardinality.clauses:
        solver.add_clause(clause)
    status, model = solver.solve(time_limit=time_limit)
    if status is not True:
        return status, None
    return True, {
        source for source in range(source_rank) if model[source + 1]
    }


def scan(
    boundary_path: Path,
    first_target: int,
    second_target: int,
    time_limit: float,
    start_bound: int,
    stop_bound: int,
) -> dict:
    if start_bound < 0:
        raise ValueError("start bound must be nonnegative")
    if stop_bound < start_bound:
        raise ValueError("stop bound must be at least the start bound")

    rows, columns = read_binary_boundary(boundary_path)
    target = {first_target, second_target}
    seed = linear_seed(rows, target)
    verify_selected(rows, seed, target)

    lower_bound = start_bound
    best = seed
    upper_bound = len(best)
    checks = []
    for bound in range(start_bound, min(stop_bound, upper_bound - 1) + 1):
        status, candidate = bounded_solve(
            columns, len(rows), target, bound, time_limit
        )
        record = {"bound": bound, "status": str(status)}
        if status is True:
            verify_selected(rows, candidate, target)
            best = candidate
            upper_bound = len(best)
            record["support"] = upper_bound
            checks.append(record)
            break
        elif status is False:
            lower_bound = bound + 1
        else:
            checks.append(record)
            break
        checks.append(record)

    return {
        "first_target": first_target,
        "second_target": second_target,
        "start_bound": start_bound,
        "stop_bound": stop_bound,
        "linear_seed_support": len(seed),
        "lower_bound": lower_bound,
        "upper_bound": upper_bound,
        "optimal": start_bound == 0 and lower_bound == upper_bound,
        "selected_sources": sorted(best),
        "checks": checks,
        "verified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("boundary", type=Path)
    parser.add_argument("first_target", type=int)
    parser.add_argument("second_target", type=int)
    parser.add_argument("--time-limit", type=float, default=15.0)
    parser.add_argument("--start-bound", type=int, default=0)
    parser.add_argument("--stop-bound", type=int, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = scan(
        args.boundary,
        args.first_target,
        args.second_target,
        args.time_limit,
        args.start_bound,
        args.stop_bound,
    )
    serialized = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(serialized, encoding="utf-8")
    print(serialized, end="")


if __name__ == "__main__":
    main()
