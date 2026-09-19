"""Test exact cycle packets for orthogonality to cellular boundaries."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import ZZ, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    packet = json.loads(args.packet.read_bytes())
    if packet["level"] != level:
        raise ValueError("packet and cellular levels differ")

    records = []
    for index, source in enumerate(packet["exact_short_homology_circuits"]):
        cycle = vector(ZZ, dimensions[2])
        for entry in source["coordinates"]:
            cycle[entry["coordinate"]] = entry["coefficient"]
        cycle_residual = boundaries[2].transpose() * cycle.column()
        boundary_pairing = boundaries[3] * cycle.column()
        records.append({
            "packet_index": index,
            "kernel_row": source["kernel_row"],
            "cycle_residual_zero": not bool(cycle_residual),
            "boundary_pairing_zero": not bool(boundary_pairing),
            "boundary_pairing_support": sum(
                1 for value in boundary_pairing.column(0) if value),
            "boundary_pairing_l2_squared": int(sum(
                value * value for value in boundary_pairing.column(0))),
            "boundary_pairing_maximum_absolute_coefficient": max(
                (abs(int(value)) for value in boundary_pairing.column(0)),
                default=0),
        })
    certificate = {
        "level": level,
        "packet": str(args.packet),
        "records": records,
        "harmonic_packet_rank": sum(
            record["boundary_pairing_zero"] for record in records),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps(certificate, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
