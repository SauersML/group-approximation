#!/usr/bin/env python3
"""Fourth pass on CANDIDATE records: finite quotients P(T)/<<g^n>> found by GAP coset enumeration.

For a CANDIDATE record (with its Tietze-reduced presentation from soficcert.py) and every remaining generator g and
n = 1..NMAX, GAP builds Q = <remaining | reduced relators, g^n>. When |Q| <= ORDMAX, a faithful permutation
representation of Q is pulled back to the ORIGINAL generators through the substitution words, and the record
becomes RESOLVED when this single witness separates every derived-distinct pair of reverse cells. verify.py then
checks the witness against the original relators, exactly as for the other passes.

Usage: finitewitness.py ns nm sofic_or_candidate.jsonl latest_pass.jsonl out.jsonl [NMAX ORDMAX]
  sofic_or_candidate.jsonl  soficcert.py output (supplies the reduced presentation of each candidate)
  latest_pass.jsonl         the latest pass output for the same ids (supplies rev_classes and status)
"""
import json
import os
import subprocess
import sys
import tempfile

GAP_TEMPLATE = r"""
SetPrintFormattingStatus("*stdout*", false);
F := FreeGroup(%(ngen)d);;
g := GeneratorsOfGroup(F);;
W := function(w) local r, x; r := One(F); for x in w do if x > 0 then r := r * g[x]; else r := r * g[-x]^-1; fi; od; return r; end;;
rels := List(%(rels)s, W);;
defs := List(%(defs)s, W);;
cells := %(cells)s;;
FwSearch := function()
  local gi, n, G, tab, s, hom, P, d, img, cimg, p;
  for gi in [1..Length(g)] do
    for n in [1..%(nmax)d] do
      G := F / Concatenation(rels, [g[gi]^n]);
      if 0 in AbelianInvariants(G) then continue; fi;
      tab := CosetTableFromGensAndRels(FreeGeneratorsOfFpGroup(G), RelatorsOfFpGroup(G), [] : max := %(cosetmax)d, silent := true);
      if tab = fail then continue; fi;
      s := Length(tab[1]);
      if s > %(ordmax)d then continue; fi;
      hom := IsomorphismPermGroup(G);
      hom := hom * SmallerDegreePermutationRepresentation(Image(hom));
      P := Image(hom);
      d := Maximum(1, LargestMovedPoint(P));
      img := List(defs, w -> Image(hom, MappedWord(w, g, GeneratorsOfGroup(G))));
      cimg := List(cells, c -> Product(List(c, k -> img[k]), One(P)));
      if Length(Set(cimg)) = %(nclasses)d then
        Print("WITNESS ", gi, " ", n, " ", s, " ", d, "\n");
        for p in img do Print("PERM ", List(ListPerm(p, d), x -> x - 1), "\n"); od;
        return;
      fi;
    od;
  od;
end;;
FwSearch();
QUIT;
"""


def main():
    ns, nm = int(sys.argv[1]), int(sys.argv[2])
    fsc, flatest, fout = sys.argv[3], sys.argv[4], sys.argv[5]
    nmax = int(sys.argv[6]) if len(sys.argv) > 6 else 30
    ordmax = int(sys.argv[7]) if len(sys.argv) > 7 else 20000
    ng = ns - 1 + nm - 1
    pres = {}
    for line in open(fsc):
        r = json.loads(line)
        if r["status"] == "CANDIDATE":
            pres[r["id"]] = r["tietze"]
    stats = {}
    with open(fout, "w") as fh:
        for line in open(flatest):
            r = json.loads(line)
            if r["status"] != "CANDIDATE":
                continue
            t = pres[r["id"]]
            # relabel the remaining generators 1..k (only they occur in the relators and substitution words)
            lab = {h: i + 1 for i, h in enumerate(t["remaining"])}
            rl = lambda w: [lab[x] if x > 0 else -lab[-x] for x in w]
            defs = [rl(t["defs"][str(k)]) for k in range(1, ng + 1)]
            # reverse cell x_m x_s as a list of original generator numbers (1-based)
            cells = [([ns - 1 + m] if m else []) + ([s] if s else []) for m in range(nm) for s in range(ns)]
            src = GAP_TEMPLATE % {"ngen": len(lab), "rels": json.dumps([rl(q) for q in t["relators"]]),
                                  "defs": json.dumps(defs), "cells": json.dumps(cells),
                                  "nclasses": len(r["rev_classes"]), "nmax": nmax, "ordmax": ordmax,
                                  "cosetmax": 50 * ordmax}
            with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as tf:
                tf.write(src)
            try:
                out = subprocess.run(["gap", "-q", tf.name], stdin=subprocess.DEVNULL, capture_output=True,
                                     text=True, timeout=600).stdout
            except subprocess.TimeoutExpired:
                out = ""
            os.unlink(tf.name)
            lines = out.split("\n")
            wl = [q for q in lines if q.startswith("WITNESS")]
            if wl:
                _, gi, n, size, d = wl[0].split()
                gi = t["remaining"][int(gi) - 1]
                perms = [json.loads(q[5:].replace(" ", "")) for q in lines if q.startswith("PERM")]
                rec = {k: v for k, v in r.items() if k not in ("unseparated",)}
                rec["witnesses"] = r.get("witnesses", []) + [{"degree": int(d), "gens": perms,
                                                              "quotient": {"power_of": int(gi), "n": int(n),
                                                                           "order": int(size)}}]
                rec["status"] = "RESOLVED"
            else:
                rec = r
            stats[rec["status"]] = stats.get(rec["status"], 0) + 1
            fh.write(json.dumps(rec) + "\n")
            print(r["id"], rec["status"], flush=True)
    print("finitewitness", stats, flush=True)


if __name__ == "__main__":
    main()
