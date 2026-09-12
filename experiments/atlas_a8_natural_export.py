"""Emit GAP code for the natural eight-point A8 chart representation.

The two-chart atlas is written in GL(4,2) coordinates.  GAP supplies an
explicit exceptional isomorphism GL(4,2) ~= A8; this exporter asks GAP for
the corresponding natural eight-point permutation for every matrix occurring
in the atlas constraint family.  The resulting JSON is consumed by the
one-involution experiment, so no numerical guess of the isomorphism enters.
"""

import numpy as np

import atlas_outer_scan_export as outer
import atlas_two_chart_search as atlas


BEST_INNER_ALIGNMENT = np.array(
    [[0, 0, 0, 1],
     [0, 1, 0, 0],
     [0, 0, 1, 0],
     [1, 0, 0, 0]], dtype=np.uint8)


def main():
    relation_names, relations = atlas.relation_family()
    atlas.validate_relation_words(relation_names, relations)

    matrices = {}
    factor_generators = atlas.factor_generators()
    for relation in relations:
        for _, generator in factor_generators:
            for _, matrix in atlas.commutator(generator, relation):
                matrices.setdefault(atlas.matrix_key(matrix).hex(), matrix)
    for _, word in factor_generators:
        for _, matrix in word + atlas.inverse(word):
            matrices.setdefault(atlas.matrix_key(matrix).hex(), matrix)
    matrices.setdefault(atlas.matrix_key(BEST_INNER_ALIGNMENT).hex(),
                        BEST_INNER_ALIGNMENT)

    generators = [word[0][1] for _, word in factor_generators[:6]]
    print("G:=Group([%s]);; A:=AlternatingGroup(8);;" %
          ",".join(outer.gap_perm(g) for g in generators))
    print("iso:=IsomorphismGroups(G,A);;")
    print("Print(\"{\\\"matrices\\\":{\");;")
    keys = sorted(matrices)
    for index, key in enumerate(keys):
        separator = "" if index == 0 else ","
        print("Print(%s,\"\\\"%s\\\":\",List([1..8],i->i^Image(iso,%s)));;" %
              (outer.gap_string(separator), key,
               outer.gap_perm(matrices[key])))
    print("Print(\"}}\\n\");; QUIT;")


if __name__ == "__main__":
    main()
