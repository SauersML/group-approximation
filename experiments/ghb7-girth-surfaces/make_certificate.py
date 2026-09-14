#!/usr/bin/env python3
"""Extract one labelling for every orientable T=24 girth surface that has one (from sol24.json)."""
import json
import ghb7_girth_surfaces as g

D = json.load(open("surf24.json")); R = json.load(open("sol24.json")); certs = []
for z in R:
    if z["solutions"] and z["orientable"]:
        r = D["surfaces"][z["n"]]; x = z["first"][0]
        assert g.verify(r, 24, x)
        edges, _ = g.structure(r, 24)
        certs.append({"surface_index": z["n"], "T": 24, "r0": r[0], "r1": r[1], "r2": r[2],
                      "labels": [[k, t, s, x[e]] for e, (k, t, s) in enumerate(edges)]})
conv = ("chambers 0..T-1; r_k = side-k gluing; label [k,t,s,x] with t<s=r_k(t): crossing from t to s "
        "multiplies by g_k^x and from s to t by g_k^-x, where g_0=c, g_1=a, g_2=b; vertex of type i "
        "is an orbit of <r_j,r_k> with {i,j,k}={0,1,2}; vertex groups X_0=<a,b>, X_1=<c,b>, X_2=<c,a>")
json.dump({"convention": conv, "certificates": certs}, open("certificates-genus2.json", "w"), indent=1)
print("certificates", len(certs), [c["surface_index"] for c in certs])
