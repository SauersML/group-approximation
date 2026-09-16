#!/usr/bin/env python3
"""Census of non-doubling subsets of S_(3,5), the nine monomials of Guba's Problem P_(2,2).

Search space (exact).  S_(3,5) = { x_i x_j : i <= j, i <= 2, j <= 3 } (nine normal forms of
degree 2).  For every k-element subset S of S_(3,5) and every degree D = D_lo, ..., DMAX this
script asks whether some Y inside the finite universe M_(D, R_S(D)) has |S Y| < 2|Y|, where
R_S(D) = max over s in S, t in {1,2} of (s_t + D + 2 - t).  By the established claim
thompson-f-monomial-doubling-ratio-is-a-finite-computation (item 1), such a Y exists in that
universe iff it exists anywhere in M_D, i.e. iff Lambda_S(D) < 2.  D_lo is the largest recorded
D* of a (k-1)-element subset (a witness for S at degree D is one for every subset of S).
The first degree with a witness is recorded as D*; the smallest minimizer Y* of |S Y| - 2|Y|
(canonical, independent of the max-flow found) is recounted by verify_witness.py, which shares
no code with witness_flow.cpp, and its sha256 is recorded.  Y* files with at most KEEP words
are stored gzipped under certs/.

Usage: census.py K DMAX [FIRST LAST]   (subset indices FIRST..LAST-1 in itertools order)
Appends JSON lines to results_k{K}.jsonl and skips subsets already present.
Usage: census.py extend K DMAX [FIRST LAST]
Continues every recorded subset in the range with no witness and searched[1] < DMAX, from degree
searched[1] + 1, and rewrites results_k{K}.jsonl.
Usage: census.py regen K
Recomputes Y* for every certified record with Y <= KEEP and no stored certificate, checks its size and
sha256 against the record, and stores it.
"""
import gzip, itertools, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify_witness as vw  # noqa: E402

S35 = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]
KEEP = 40000
BIN = os.environ.get("WITNESS_FLOW", os.path.join(HERE, "witness_flow"))
TMP = os.environ.get("CENSUS_TMP", "/tmp")


def spec(S):
    return ";".join(",".join(str(x) for x in s) for s in S)


def universe_bound(S, D):
    return max(s[t] + D + len(s) - (t + 1) for s in S for t in range(len(s)))


def load(path):
    out = {}
    if os.path.exists(path):
        for line in open(path):
            if line.strip():
                r = json.loads(line)
                out[tuple(r["subset"])] = r
    return out


def run_flow(k, idx, S, D):
    """Return (info, raw certificate or None)."""
    L = universe_bound(S, D)
    cert = os.path.join(TMP, "census_cert_%d_%s.txt" % (k, "".join(map(str, idx))))
    env = dict(os.environ, CERT=cert)
    out = subprocess.run([BIN, str(D), str(L), spec(S)], capture_output=True, text=True, env=env, check=True)
    info = json.loads(out.stdout)
    assert info["L"] == L
    raw = None
    if info["found"]:
        raw = open(cert, "rb").read()
        os.remove(cert)
    return info, raw


def store(k, idx, D, raw):
    name = "k%d_%s_D%d.txt.gz" % (k, "".join(map(str, idx)), D)
    with open(os.path.join(HERE, "certs", name), "wb") as f:
        f.write(gzip.compress(raw, mtime=0))
    return "certs/" + name


def search(k, idx, rec, d_from, dmax):
    S = [S35[i] for i in idx]
    for D in range(d_from, dmax + 1):
        info, raw = run_flow(k, idx, S, D)
        rec["searched"][1] = D
        if raw is not None:
            ny, nsy, h = vw.check(raw, S, D)
            assert ny == info["Y"] and nsy == info["SY"] and nsy < 2 * ny, (info, ny, nsy)
            rec.update(Dstar=D, L=info["L"], U=info["U"], Y=ny, SY=nsy, sha256=h)
            if ny <= KEEP:
                rec["cert"] = store(k, idx, D, raw)
            return


def main():
    mode = "new"
    if sys.argv[1] in ("extend", "regen"):
        mode = sys.argv.pop(1)
    k = int(sys.argv[1])
    subsets = list(itertools.combinations(range(9), k))
    outp = os.path.join(HERE, "results_k%d.jsonl" % k)
    done = load(outp)
    os.makedirs(os.path.join(HERE, "certs"), exist_ok=True)
    vw.selftest()
    if mode == "regen":
        for idx, r in sorted(done.items()):
            if r["Dstar"] is None or "cert" in r or r["Y"] > KEEP:
                continue
            S = [S35[i] for i in idx]
            info, raw = run_flow(k, idx, S, r["Dstar"])
            ny, nsy, h = vw.check(raw, S, r["Dstar"])
            assert (ny, nsy, h) == (r["Y"], r["SY"], r["sha256"]), (idx, ny, nsy, h)
            r["cert"] = store(k, idx, r["Dstar"], raw)
            print("regen", r["monomials"], ny, nsy, flush=True)
        rewrite(outp, done)
        return
    dmax = int(sys.argv[2])
    first = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    last = int(sys.argv[4]) if len(sys.argv) > 4 else len(subsets)
    if mode == "extend":
        for idx in subsets[first:last]:
            r = done.get(idx)
            if r is None or r["Dstar"] is not None or r["searched"][1] >= dmax:
                continue
            t0 = time.time()
            search(k, idx, r, r["searched"][1] + 1, dmax)
            r["seconds"] = round(r["seconds"] + time.time() - t0, 2)
            rewrite(outp, done)
            print(json.dumps(r), flush=True)
        return
    prev = load(os.path.join(HERE, "results_k%d.jsonl" % (k - 1))) if k > 3 else {}
    for idx in subsets[first:last]:
        if idx in done:
            continue
        S = [S35[i] for i in idx]
        d_lo = 1
        for sub in itertools.combinations(idx, k - 1):
            r = prev.get(sub)
            if r is not None and r.get("Dstar") is not None:
                d_lo = max(d_lo, r["Dstar"])
        rec = {"subset": list(idx), "monomials": spec(S), "Dstar": None, "searched": [d_lo, d_lo - 1]}
        t0 = time.time()
        search(k, idx, rec, d_lo, dmax)
        rec["seconds"] = round(time.time() - t0, 2)
        with open(outp, "a") as f:
            f.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)


def rewrite(outp, done):
    tmp = outp + ".tmp"
    with open(tmp, "w") as f:
        for idx in sorted(done):
            f.write(json.dumps(done[idx]) + "\n")
    os.replace(tmp, outp)


if __name__ == "__main__":
    main()
