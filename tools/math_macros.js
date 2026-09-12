(function (root, factory) {
  'use strict';
  var macros = factory();
  if (typeof module === 'object' && module.exports) module.exports = macros;
  if (root) root.CAIRN_MATH_MACROS = macros;
}(typeof window === 'undefined' ? null : window, function () {
  'use strict';
  return Object.freeze({
    '\\C': '\\mathbb{C}',
    '\\F': '\\mathbb{F}',
    '\\Z': '\\mathbb{Z}',
    '\\R': '\\mathbb{R}',
    '\\N': '\\mathbb{N}',
    '\\SL': '\\operatorname{SL}',
    '\\GL': '\\operatorname{GL}',
    '\\EL': '\\operatorname{EL}',
    '\\U': '\\mathcal{U}',
    '\\Fix': '\\operatorname{Fix}',
    '\\tr': '\\operatorname{tr}',
    '\\Ad': '\\operatorname{Ad}',
    '\\End': '\\operatorname{End}',
    '\\Cl': '\\operatorname{Cl}',
    '\\Rad': '\\operatorname{Rad}',
    '\\Cmax': 'C^*_{\\mathrm{max}}',
    '\\Cred': 'C^*_{\\mathrm{r}}',
    '\\opnorm': '\\left\\lVert #1\\right\\rVert',
    '\\hsnorm': '\\left\\lVert #1\\right\\rVert_{2}',
    '\\normal': '\\left\\langle\\!\\left\\langle #1\\right\\rangle\\!\\right\\rangle',
    '\\varinjlim': '\\mathop{\\underset{\\longrightarrow}{\\lim}}',
    '\\textup': '\\text{#1}'
  });
}));
