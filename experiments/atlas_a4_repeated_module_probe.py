#!/usr/bin/env sage
"""Exact centralizer sizes for the first repeated natural A8 module."""

from sage.all import GF, GL, Matrix, libgap

from atlas_a4_19243_component_localization import H6_LABELS, order
from atlas_two_chart_search import factor_generators


def lift(matrix):
    entries = []
    for row in matrix:
        for multiplicity_row in range(2):
            for entry in row:
                for multiplicity_column in range(2):
                    entries.append(int(entry) if multiplicity_row == multiplicity_column else 0)
    return Matrix(GF(2), 8, 8, entries)


ambient = GL(8, 2)
h6 = [lift(value) for value in H6_LABELS if order(value) == 2]
a8 = [lift(word[0][1]) for _, word in factor_generators() if word[0][0] == 1]
h6_group = libgap.Group([value._libgap_() for value in h6])
a8_group = libgap.Group([value._libgap_() for value in a8])
h6_centralizer = libgap.Centralizer(ambient, h6_group)
a8_centralizer = libgap.Centralizer(ambient, a8_group)

print({
    "h6_group_order": int(libgap.Size(h6_group)),
    "a8_group_order": int(libgap.Size(a8_group)),
    "h6_centralizer_order": int(libgap.Size(h6_centralizer)),
    "a8_centralizer_order": int(libgap.Size(a8_centralizer)),
    "effective_h6_gauges": int(libgap.Index(h6_centralizer, a8_centralizer)),
})
