#!/usr/bin/env python3
"""Exact finiteness certificate for H = <S, T> through a finite presentation.

GAP computes the image H_n of H on level n and a finite presentation <S, T | r_1..r_k> of H_n
(the presented group has order |H_n|).  The script then checks that every r_i is trivial in
G (exact triviality test).  Then H is a quotient of the presented group, which is H_n, and H_n
is a quotient of H: so H = H_n is finite of that order.  If a relator fails, level n + 1 is used.
Usage: python3 h_present.py NAMEFILE [LEVELS [GAP_TIMEOUT]] > h_present.out  (NAMEFILE: one name per line; LEVELS e.g. 2,3)
"""
import sys, subprocess, tempfile, os
from bouquets import bouquets, Levels, cycles_str
from loopgraph import reduce, inv

def gap_presentation(R, I, n):
    Lv = Levels(R, n)
    s, t = cycles_str(Lv.word(I["S"], n)), cycles_str(Lv.word(I["T"], n))
    prog = (f"s:={s};; t:={t};; H:=Group(s,t);; hom:=IsomorphismFpGroupByGenerators(H,[s,t]);;\n"
            "Print(Size(H),\"\\n\");\n"
            "for r in RelatorsOfFpGroup(Range(hom)) do Print(LetterRepAssocWord(r),\"\\n\"); od;\nQUIT;\n")
    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as f: f.write(prog); path = f.name
    try: out = subprocess.run(["gap", "-q", "-o", "2g", path], capture_output=True, text=True, timeout=GAP_TIMEOUT).stdout
    except subprocess.TimeoutExpired: out = ""
    os.unlink(path)
    if not out.split(): return None, []
    lines = [l.strip() for l in out.replace("\\\n", "").split("\n") if l.strip()]
    order = int(lines[0]); rels = []
    buf = ""
    for l in lines[1:]:
        buf += l
        if buf.endswith("]"):
            rels.append([int(x) for x in buf.strip("[] ").split(",") if x.strip()]); buf = ""
    return order, rels

def certify(R, I, levels=(2, 3, 4)):
    gen = {1: I["S"], -1: inv(I["S"]), 2: I["T"], -2: inv(I["T"])}
    for n in levels:
        order, rels = gap_presentation(R, I, n)
        if order is None: continue
        bad = None
        for r in rels:
            w = reduce(sum((gen[x] for x in r), ()))
            try:
                if not R.trivial(w): bad = r; break
            except RuntimeError: bad = r; break
        if bad is None: return order, n, len(rels), max(map(len, rels))
    return None, n, None, None

GAP_TIMEOUT = int(sys.argv[3]) if len(sys.argv) > 3 else 1200
LEVELS = tuple(int(x) for x in sys.argv[2].split(",")) if len(sys.argv) > 2 else (2, 3, 4)
if __name__ == "__main__":
    want = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    cases = {name: (R, I) for name, R, I in bouquets() if name in set(want)}
    for name in want:
        R, I = cases[name]
        order, n, k, m = certify(R, I, LEVELS)
        print(name, "|", f"FINITE |H| = {order} (presentation of H_{n}: {k} relators, max length {m}, all trivial in G)"
              if order else f"no certificate at levels {LEVELS}", flush=True)
