/* Rewrite LaTeX math that KaTeX does not accept into equivalent KaTeX input.
   mathtools adds matrix environments with built-in delimiters and starred
   variants with an alignment option; KaTeX has neither.  Applied to every
   formula before rendering, in the paper edition and in the explainer. */
(function (root, factory) {
  'use strict';
  var normalize = factory();
  if (typeof module === 'object' && module.exports) module.exports = normalize;
  if (root) root.CAIRN_MATH_NORMALIZE = normalize;
}(typeof window === 'undefined' ? null : window, function () {
  'use strict';
  var DELIMS = { p: ['(', ')'], b: ['[', ']'], B: ['\\{', '\\}'], v: ['|', '|'], V: ['\\|', '\\|'] };
  function normalizeTex(src) {
    if (typeof src !== 'string' || src.indexOf('\\begin{') < 0) return src;
    // \begin{pmatrix*}[r] ... \end{pmatrix*}  ->  \begin{pmatrix} ... \end{pmatrix}
    src = src.replace(/\\begin\{([pbBvV]?(?:small)?matrix)\*\}(?:\[[lcr]\])?/g, '\\begin{$1}')
             .replace(/\\end\{([pbBvV]?(?:small)?matrix)\*\}/g, '\\end{$1}');
    // \begin{psmallmatrix} ... \end{psmallmatrix}  ->  \left(\begin{smallmatrix} ... \end{smallmatrix}\right)
    src = src.replace(/\\begin\{([pbBvV])smallmatrix\}/g, function (m, d) {
      return '\\left' + DELIMS[d][0] + '\\begin{smallmatrix}';
    }).replace(/\\end\{([pbBvV])smallmatrix\}/g, function (m, d) {
      return '\\end{smallmatrix}\\right' + DELIMS[d][1];
    });
    return src;
  }
  return normalizeTex;
}));
