#!/usr/bin/env python3
"""Independent check of reported strict rectangle data, by direct evaluation.

Reads JSON lines with fields mu, nu, y, fwd, rev (as written by satcensus.py for satisfiable
instances), plus the alphabet size q and the shape. It does not reuse satcensus.py: rules are
turned into dictionaries keyed by symbol tuples, assignments are dictionaries keyed by cells, and
every T_f-constant assignment is evaluated for Dec and every T_r-constant assignment for Enc.

A record passes when Dec holds on all T_f-constant assignments, the reported y breaks Enc, and
the number of breaking assignments is positive. Prints one JSON summary line.

Usage: checkmodel.py sat_records.jsonl q ns nm
"""
import itertools, json, sys


def rule_dict(values, q, arity):
    keys = list(itertools.product(range(q), repeat=arity))
    assert len(keys) == len(values), (len(keys), len(values))
    return dict(zip(keys, values))


def assignments(classes, q):
    for vals in itertools.product(range(q), repeat=len(classes)):
        a = {}
        for blk, x in zip(classes, vals):
            for c in blk:
                a[c] = x
        yield a


def check(rec, q, ns, nm):
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    mu = rule_dict(rec["mu"], q, nm)
    nu = rule_dict(rec["nu"], q, ns)
    dec_fail = 0
    for p in assignments(rec["fwd"], q):
        relays = tuple(mu[tuple(p[f"{s}|{m}"] for m in M)] for s in S)
        if nu[relays] != p["1|1"]:
            dec_fail += 1
    enc_fail = 0
    for y in assignments(rec["rev"], q):
        relays = tuple(nu[tuple(y[f"{m}|{s}"] for s in S)] for m in M)
        if mu[relays] != y["1|1"]:
            enc_fail += 1
    given = {}
    for blk, x in zip(rec["rev"], rec["y"]):
        for c in blk:
            given[c] = x
    relays = tuple(nu[tuple(given[f"{m}|{s}"] for s in S)] for m in M)
    given_breaks = mu[relays] != given["1|1"]
    return {"pair": rec.get("pair"), "dec_failures": dec_fail, "enc_failures": enc_fail,
            "given_y_breaks_enc": given_breaks, "ok": dec_fail == 0 and enc_fail > 0 and given_breaks}


def main():
    path, q, ns, nm = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    res = [check(r, q, ns, nm) for r in map(json.loads, open(path)) if r.get("sat")]
    print(json.dumps({"records": len(res), "ok": sum(r["ok"] for r in res),
                      "not_ok": [r for r in res if not r["ok"]][:5]}))


if __name__ == "__main__":
    main()
