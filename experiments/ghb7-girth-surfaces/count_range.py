#!/usr/bin/env python3
"""Uncapped labelling counts for chosen T=24 girth-surface classes.
usage: count_range.py n1 n2 ...   (reads surf24.json; the first uncapped run stopped after class 65)"""
import sys, json, time
import ghb7_girth_surfaces as g

D = json.load(open("surf24.json")); T = D["T"]
W = {i: g.words_by_product(i, 2 * g.M[i], {0})[0] for i in range(3)}
MK = {i: g.masks_for(W[i], 2 * g.M[i]) for i in range(3)}
for n in map(int, sys.argv[1:]):
    t0 = time.time(); r = D["surfaces"][n]
    edges, verts = g.structure(r, T)
    sols, nodes = g.solve(edges, verts, [MK[i][0] for i, _ in verts], [MK[i][1] for i, _ in verts], 10 ** 7)
    print("surface", n, "orientable", D["orientable"][n], "solutions", len(sols), "divisible by 216", len(sols) % 216 == 0,
          "nodes", nodes, "verified first 50", all(g.verify(r, T, s) for s in sols[:50]),
          "sec", round(time.time() - t0, 1), flush=True)
