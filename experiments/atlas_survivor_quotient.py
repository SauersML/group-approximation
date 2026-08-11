"""Build exact GAP quotients from perfect-overlap survivor relations.

The first atlas boundary survivors lie in two copies of
H=diag(GL(3,2),1).  This utility reads the exact survivor artifact emitted by
atlas_perfect_overlap_scan.py, translates the selected 3 x 3 matrices into a
finitely presented H*H, and asks GAP about the quotient obtained by setting
the survivor words equal to one.

Finite output with both factor images of order 168 gives an exact finite
identity model for the selected survivor relations.  Collapse of a factor
rules out that particular identity quotient as an atlas model.  Failure to
finish is intentionally inconclusive; callers should enforce a short timeout.
"""

import argparse
import json
import subprocess

import numpy as np


def gap_rows(matrix):
    return "[" + ",".join(
        "[" + ",".join(str(int(value)) for value in row) + "]"
        for row in matrix
    ) + "]"


def matrix_from_record(letter):
    matrix = np.frombuffer(
        bytes.fromhex(letter["matrix_f2_hex"]), dtype=np.uint8
    ).reshape(4, 4)
    if (not np.array_equal(matrix[3], np.array((0, 0, 0, 1)))
            or not np.array_equal(matrix[:, 3], np.array((0, 0, 0, 1)))):
        raise ValueError("survivor letter is outside diag(GL(3,2),1)")
    return matrix[:3, :3]


def selected_records(data, representatives_only):
    records = data["survivor_records"]
    if not representatives_only:
        return records
    representatives = {}
    for record in records:
        representatives.setdefault(tuple(record["projection_pair"]), record)
    return [representatives[key] for key in sorted(representatives)]


def gap_source(records):
    relators = []
    for record in records:
        letters = []
        for letter in record["word"]:
            matrix = gap_rows(matrix_from_record(letter))
            embedding = "e%d" % letter["factor"]
            letters.append("Image(%s,Image(iso,FindH(%s)))" % (
                embedding, matrix))
        relators.append("*".join(letters))

    return """
H:=GL(3,2);;
elementsH:=Elements(H);;
FindH:=function(rows)
  local h;
  for h in elementsH do
    if List(h,row->List(row,IntFFE))=rows then
      return h;
    fi;
  od;
  Error("matrix not found in GL(3,2)");
end;;
iso:=IsomorphismFpGroup(H);;
FH:=Image(iso);;
P:=FreeProduct(FH,FH);;
e1:=Embedding(P,1);;
e2:=Embedding(P,2);;
rels:=[%s];;
Q:=P/rels;;
nat:=GroupHomomorphismByImages(
  P,Q,GeneratorsOfGroup(P),GeneratorsOfGroup(Q));;
factor1:=Image(nat,Image(e1,FH));;
factor2:=Image(nat,Image(e2,FH));;
Print("relators=%s\\n");
Print("quotient_size=",Size(Q),"\\n");
Print("factor1_size=",Size(factor1),"\\n");
Print("factor2_size=",Size(factor2),"\\n");
Print("abelian_invariants=",AbelianInvariants(Q),"\\n");
QUIT;
""" % (",".join(relators), len(relators))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("--representatives-only", action="store_true")
    parser.add_argument("--gap", default="sage -gap -q")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as stream:
        data = json.load(stream)
    records = selected_records(data, args.representatives_only)
    completed = subprocess.run(
        args.gap.split(), input=gap_source(records), text=True, check=False)
    raise SystemExit(completed.returncode)


if __name__ == "__main__":
    main()
