import sys, json, runpy, io, contextlib
sys.argv = ["spineG.py", "60", "12"]
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    G = runpy.run_path("spineG.py")
for S in sorted(G["spine"].values(), key=lambda S: (len(S), sorted(S))):
    print(json.dumps({"size": len(S), "cells": sorted(map(list, S))}))
