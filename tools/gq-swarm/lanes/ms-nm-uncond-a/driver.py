# Instrumented copy of sentence_census.verify_unconditional: same classifier and filters, with timing and
# per-row flushed output, rows with tex line <= 1300 first. Read-only; runs in the snapshot dir.
import sys, time, os
sys.path.insert(0, "scripts")
import sentence_census as sc
from pathlib import Path
import importlib
t0 = time.time()
rows, probes = sc.load_ledger(sc.LEDGER)
records = sc.extract(sc.TEX)
sc.attach_anchors(records, sc.TEX, probes)
records = sc.join(records, sc.load_map(sc.MAP), rows, True)
print(f"records {len(records)} in {time.time()-t0:.1f}s", flush=True)
m = importlib.import_module("check_non_mf_unconditional")
from lean_decls import build_index
t1 = time.time(); corpus = m.build_corpus(Path(sc.ROOT)); print(f"corpus {time.time()-t1:.1f}s", flush=True)
t1 = time.time(); paths = build_index(Path(sc.ROOT)); print(f"index {time.time()-t1:.1f}s", flush=True)
roster, _ = m.read_roster(Path(sc.ROOT) / m.DEFAULT_ROSTER)
baseline, malformed = sc.read_conditional_baseline(sc.DEFAULT_CONDITIONAL_BASELINE)
qm = {}
def line(r):
    try: return int(r.get("line") or 0)
    except Exception: return 0
order = sorted(records, key=lambda r: (line(r) > 1300, line(r)))
matched = set(); n = 0
for r in order:
    if r["status"] not in {"formalized", "definition", "partial"}: continue
    n += 1
    for name in r["decls"].split():
        path = paths.get(name)
        if path is not None and path not in qm:
            qm[path] = m.scan_module(path, qualified=True)
        decl = qm.get(path, {}).get(name)
        if decl is None: continue
        for det, detail in m.classify(corpus, decl, roster, name):
            if not sc.counts_finding(r["status"], det): continue
            tag = "ACCEPTED" if (det, name) in baseline else "NEW"
            if tag == "ACCEPTED": matched.add((det, name))
            print(f"{tag}\t{r['key']}\tl{line(r)}\t{det}\t{name}\t{detail[:200]}", flush=True)
    if n % 50 == 0: print(f"progress rows={n} t={time.time()-t0:.0f}s", flush=True)
for e in sorted(set(baseline) - matched): print(f"STALE\t{e[0]}\t{e[1]}", flush=True)
print(f"DONE rows={n} t={time.time()-t0:.0f}s", flush=True)
