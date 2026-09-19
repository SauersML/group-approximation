#!/usr/bin/env python3
"""Orders |H_1|, |H_2|, |H_3| of the images of H = <S, T> on levels 1, 2, 3 (GAP), for the
recursions named in NAMEFILE.  Stable orders (|H_2| = |H_3|) select the candidates for the
presentation certificate h_present.py; growing orders are recorded as data only.
Usage: python3 h_orders.py NAMEFILE > h_orders.out   (output: name | o1 o2 o3 | seconds)
"""
import sys, subprocess, tempfile, os, time
from bouquets import bouquets, Levels, cycles_str

if __name__ == "__main__":
    want = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    cases = {n: (R, I) for n, R, I in bouquets() if n in set(want)}
    for name in want:
        R, I = cases[name]; Lv = Levels(R, 3); t0 = time.time()
        prog = "".join(f"Print(Size(Group({cycles_str(Lv.word(I['S'], n))},{cycles_str(Lv.word(I['T'], n))})),\"\\n\");\n"
                       for n in (1, 2, 3)) + "QUIT;\n"
        with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as f: f.write(prog); p = f.name
        try: out = subprocess.run(["gap", "-q", "-o", "2g", p], capture_output=True, text=True, timeout=600).stdout
        except subprocess.TimeoutExpired: out = "timeout"
        os.unlink(p); print(name, "|", " ".join(out.split()), "|", round(time.time() - t0), flush=True)
