#!/usr/bin/env python3
"""Check a JSON certificate over R^x, R = L_{F_2}(1,2).

    python3 certcheck.py CERT.json [CERT2.json ...] [--no-dual] [--expect]

Exit status 0: every certificate PASSES (with --expect, every outcome matches
the file's "expect" field).  1: some certificate FAILS.  2: malformed input.

Certificate types (see README.md for the full formats):
  kaplansky-df               alpha beta = 1 and beta alpha != 1 in F_2[R^x]
  stable-finiteness          A B = I and B A != I for d x d matrices over F_2[R^x]
  gottschalk-ca              sigma o tau = id and a Garden-of-Eden pattern for tau
  kl-equation                a nontrivial coefficient in the normal closure of a
                             nonsingular one-variable equation
  normal-closure-membership  the same without nonsingularity (controls only)
"""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import leavitt as L  # noqa: E402
import groupalg as GA  # noqa: E402
import ca as CA  # noqa: E402
import kl as KL  # noqa: E402


class CertificateError(ValueError):
    pass


def _name_ok(name):
    return (isinstance(name, str) and name and not name.startswith("@") and name != "x"
            and not any(ch.isspace() or ch in "^[]()" for ch in name))


def build_units(spec):
    units = dict(L.standard_units())
    if spec is None:
        return units
    if not isinstance(spec, dict):
        raise CertificateError("'units' must be an object")
    for name, entry in spec.items():
        if not _name_ok(name):
            raise CertificateError("bad unit name %r" % (name,))
        if name in units:
            raise CertificateError("unit %r defined twice" % (name,))
        if not isinstance(entry, dict):
            raise CertificateError("unit %r must be an object" % (name,))
        if set(entry) == {"val", "inv"}:
            unit = L.Unit(L.elem_from_json(entry["val"]), L.elem_from_json(entry["inv"]))
        elif set(entry) == {"word"}:
            unit = parse_unit_word(entry["word"], units)
        elif set(entry) == {"thompson"}:
            unit = L.thompson_unit(entry["thompson"]["domain"], entry["thompson"]["range"])
        elif set(entry) == {"corner_matrix"}:
            unit = L.corner_matrix_unit(entry["corner_matrix"]["leaves"],
                                        entry["corner_matrix"]["columns"])
        elif set(entry) == {"one_plus_nilpotent"}:
            unit = L.one_plus_nilpotent(L.elem_from_json(entry["one_plus_nilpotent"]))
        else:
            raise CertificateError("unit %r: unknown definition keys %s" % (name, sorted(entry)))
        units[name] = unit
    return units


def _split_power(token):
    if "^" in token:
        base, exponent = token.split("^", 1)
        try:
            return base, int(exponent)
        except ValueError:
            raise CertificateError("bad exponent in %r" % (token,))
    return token, 1


def parse_unit_word(text, units):
    if not isinstance(text, str):
        raise CertificateError("unit words are strings, got %r" % (text,))
    result = L.IDENTITY
    for token in text.split():
        name, exponent = _split_power(token)
        if name not in units:
            raise CertificateError("unknown unit %r in %r" % (name, text))
        result = result * (units[name] ** exponent)
    return result


def parse_syllables(text, units):
    if not isinstance(text, str):
        raise CertificateError("words are strings, got %r" % (text,))
    syllables = []
    for token in text.split():
        name, exponent = _split_power(token)
        if name == "x":
            syllables.append(("x", exponent))
        elif name in units:
            syllables.append(("u", units[name] ** exponent))
        else:
            raise CertificateError("unknown syllable %r in %r" % (name, text))
    return syllables


def parse_group_algebra(value, units):
    if not isinstance(value, list):
        raise CertificateError("group algebra elements are lists of unit words")
    return GA.GroupAlgebraElement(parse_unit_word(word, units) for word in value)


def check_kaplansky_df(cert, units):
    alpha = parse_group_algebra(cert["alpha"], units)
    beta = parse_group_algebra(cert["beta"], units)
    ab = alpha * beta
    ba = beta * alpha
    lines = [
        "support |alpha| = %d, |beta| = %d" % (len(alpha), len(beta)),
        "alpha*beta has support %d; equals 1: %s" % (len(ab), ab.is_one()),
        "beta*alpha has support %d; equals 1: %s" % (len(ba), ba.is_one()),
    ]
    passed = ab.is_one() and not ba.is_one()
    if passed:
        lines.append(
            "PROVES: F_2[R^x] is not directly finite, refuting Kaplansky's direct finiteness "
            "conjecture. The linear automaton (tau_beta x)(g) = sum_{h in supp beta} x(g h) "
            "has left inverse tau_alpha and is not surjective, refuting Gottschalk's "
            "conjecture for R^x.")
    return passed, lines


def check_stable_finiteness(cert, units):
    A = [[parse_group_algebra(entry, units) for entry in row] for row in cert["A"]]
    B = [[parse_group_algebra(entry, units) for entry in row] for row in cert["B"]]
    d = len(A)
    if d == 0 or any(len(row) != d for row in A + B) or len(B) != d:
        raise CertificateError("A and B must be square matrices of the same size")
    AB = GA.matmul(A, B)
    BA = GA.matmul(B, A)
    ab_ok = GA.is_identity_matrix(AB)
    ba_ok = GA.is_identity_matrix(BA)
    lines = ["d = %d; A*B = I: %s; B*A = I: %s" % (d, ab_ok, ba_ok)]
    passed = ab_ok and not ba_ok
    if passed:
        lines.append(
            "PROVES: M_%d(F_2[R^x]) is not directly finite, so F_2[R^x] is not stably finite, "
            "refuting Kaplansky's stable finiteness conjecture over F_2 and (via linear "
            "automata on (F_2^%d)^G) Gottschalk's conjecture for R^x." % (d, d))
    return passed, lines


def _automaton(spec, k, units):
    memory = [parse_unit_word(word, units) for word in spec["memory"]]
    if "rule" in spec:
        rule = spec["rule"]
    elif "rule_bits" in spec:
        if k != 2:
            raise CertificateError("rule_bits needs alphabet 2")
        rule = [int(ch) for ch in spec["rule_bits"]]
    else:
        raise CertificateError("automaton needs 'rule' or 'rule_bits'")
    return CA.CellularAutomaton(k, memory, rule)


def check_gottschalk_ca(cert, units):
    k = int(cert["alphabet"])
    tau = _automaton(cert["tau"], k, units)
    sigma = _automaton(cert["sigma"], k, units)
    left_ok, left_info = CA.compose_is_identity(sigma, tau)
    cells = [parse_unit_word(word, units) for word in cert["orphan"]["cells"]]
    values = cert["orphan"]["values"]
    goe, goe_info = CA.garden_of_eden(tau, cells, values)
    lines = [
        "alphabet %d; |memory(tau)| = %d; |memory(sigma)| = %d" % (k, len(tau.memory), len(sigma.memory)),
        "sigma o tau = id: %s  %s" % (left_ok, left_info),
        "orphan pattern on %d cells is Garden of Eden: %s  %s" % (len(cells), goe, goe_info),
    ]
    passed = left_ok and goe is True
    if passed:
        lines.append(
            "PROVES: tau is an injective, non-surjective cellular automaton on the full shift "
            "%d^G, G = R^x, refuting Gottschalk's surjunctivity conjecture." % k)
    return passed, lines


def check_normal_closure(cert, units, require_nonsingular):
    equation = parse_syllables(cert["equation"], units)
    coefficient = parse_unit_word(cert["coefficient"], units)
    factors = []
    for factor in cert["factors"]:
        factors.append((parse_syllables(factor["conj"], units), int(factor.get("sign", 1))))
    passed, report = KL.verify_normal_closure(
        coefficient, equation, factors, require_nonsingular=require_nonsingular)
    lines = [
        "exponent sum of x in the equation: %d" % report["exponent_sum"],
        "factors: %d; reduced lengths after each: %s" % (len(factors), report["step_lengths"][:40]),
        "final reduced length: %d" % report["final_length"],
    ] + ["reason: %s" % r for r in report["reasons"]]
    if passed and require_nonsingular:
        lines.append(
            "PROVES: the nonsingular equation w(x) = 1 over R^x has no solution in any overgroup "
            "(it kills a nontrivial coefficient), refuting the Kervaire--Laudenbach conjecture; "
            "hence R^x is not hyperlinear (Nitsche--Thom).")
    elif passed:
        lines.append("PROVES: the coefficient lies in the normal closure of the equation (control).")
    return passed, lines


CHECKERS = {
    "kaplansky-df": check_kaplansky_df,
    "stable-finiteness": check_stable_finiteness,
    "gottschalk-ca": check_gottschalk_ca,
    "kl-equation": lambda cert, units: check_normal_closure(cert, units, True),
    "normal-closure-membership": lambda cert, units: check_normal_closure(cert, units, False),
}


def check_certificate(cert):
    """Return (passed, lines).  Raises CertificateError on malformed input."""
    if not isinstance(cert, dict) or cert.get("type") not in CHECKERS:
        raise CertificateError("unknown certificate type %r" % (cert.get("type") if isinstance(cert, dict) else None,))
    units = build_units(cert.get("units"))
    try:
        return CHECKERS[cert["type"]](cert, units)
    except KeyError as missing:
        raise CertificateError("missing field %s" % missing)


def check_file(path):
    with open(path) as handle:
        cert = json.load(handle)
    passed, lines = check_certificate(cert)
    return cert, passed, lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("certificates", nargs="+")
    parser.add_argument("--no-dual", action="store_true",
                        help="skip the prefix-table cross-check (faster, less evidence)")
    parser.add_argument("--expect", action="store_true",
                        help="compare each outcome with the certificate's 'expect' field")
    args = parser.parse_args(argv)
    L.set_dual(not args.no_dual)
    status = 0
    for path in args.certificates:
        print("== %s" % path)
        try:
            cert, passed, lines = check_file(path)
        except (CertificateError, L.ParseError, ValueError, TypeError) as error:
            print("RESULT: MALFORMED: %s" % error)
            status = max(status, 2)
            continue
        for line in lines:
            print("  " + line)
        outcome = "PASS" if passed else "FAIL"
        print("RESULT: %s (%s)" % (outcome, cert["type"]))
        if args.expect:
            if cert.get("expect") != outcome:
                print("EXPECTATION MISMATCH: expected %r" % (cert.get("expect"),))
                status = max(status, 1)
        elif not passed:
            status = max(status, 1)
    print("dual path: %s" % (L.dual_stats(),))
    return status


if __name__ == "__main__":
    sys.exit(main())
