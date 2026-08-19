#!/usr/bin/env python3
from pathlib import Path

p = Path("metadata/NON_MF_PROOF_LEDGER.md")
lines = p.read_text().splitlines()
out = []
seen = set()
for line in lines:
    if line.startswith("| MC.02 |"):
        seen.add("MC.02")
        marker = "  **RETARGETED 2026-08-18:"
        if marker in line and not line.endswith("|"):
            body, note = line.split(marker, 1)
            if not body.endswith("|"):
                raise SystemExit("MC.02: expected table terminator before note")
            line = body[:-1].rstrip() + " " + marker.strip() + note.rstrip() + " |"
    elif line.startswith("| PRE.19 |"):
        seen.add("PRE.19")
        marker = "  **CLOSED 2026-08-18:"
        if marker in line and not line.endswith("|"):
            body, note = line.split(marker, 1)
            if not body.endswith("|"):
                raise SystemExit("PRE.19: expected table terminator before note")
            line = body[:-1].rstrip() + " " + marker.strip() + note.rstrip() + " |"
    elif line == "| statement | 388 | 14 | 26 | 1 | 429 |":
        seen.add("statement-count")
        line = "| statement | 390 | 12 | 26 | 1 | 429 |"
    elif line == "| proof | 384 | 14 | 30 | 1 | 429 |":
        seen.add("proof-count")
        line = "| proof | 385 | 13 | 30 | 1 | 429 |"
    elif line.startswith("| p:E-exact | prose |"):
        seen.add("p:E-exact")
        line = line.replace(
            "`equivalent to exactness of the reduced group algebra`",
            "`equivalent to exactness of its reduced group $C^*$-algebra`",
            1,
        )
    elif line.startswith("| SO.16 | p:E-exact |"):
        seen.add("SO.16")
        line = line.replace(
            "C*_red(E) is exact, and so is C*_red(W)",
            "C*_red(E) is exact",
            1,
        )
        line = line.replace(
            "GHW, KWPermanence, KWExact",
            "DykemaExact, GHW, KWPermanence, KWExact",
            1,
        )
    out.append(line)

expected = {"MC.02", "PRE.19", "statement-count", "proof-count", "p:E-exact", "SO.16"}
if seen != expected:
    raise SystemExit(f"ledger normalization targets mismatch: {seen} != {expected}")
p.write_text("\n".join(out) + "\n")
