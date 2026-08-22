# Five overlap saturations authenticate the native SL3 Hecke shell

The six Weyl-conjugate index-42 parahoric charts all parameterize the same
Hecke sphere `C h C/C`.  Choosing one root chart therefore gives canonical
label bijections from the other five charts.

For each nonroot chart, sum the squared normalized-HS distances between its
42 projections and the corresponding root-chart projections.  Half of this
sum is one nonnegative scalar determined entirely by projection traces and
42 cross traces.  If all five scalars vanish, every corresponding projection
is literally equal and the root chart is one global 42-atom shell PVM.  The
sum of all chart-to-global squared errors is exactly twice the sum of the
five deficits.

Five chart comparisons are minimal: fewer edges cannot connect six charts,
and an unconnected chart component retains an independent multiplicity
conjugation invisible to all tested overlaps.

This reduces the arithmetic compiler problem to five explicit cross-chart
trace inequalities.  It does not derive them from group relators.  Once
they are controlled by mixed-root energy and first-exit mass, no further
global-label rounding is needed before applying building expansion.

