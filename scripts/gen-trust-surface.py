#!/usr/bin/env python3
"""Generate docs/trust-surface.html — the trust-surface read-through guide.

One page, one section per formalized paper (`scripts/papers.py` is the registry), each
section putting every annotated paper node beside the Lean statement that carries it.
Paper math is converted to MathML at build time (pip install latex2mathml); the page is
self-contained, no runtime JS libraries and no external assets.

The mechanical half — locate a node in the paper source, locate the Lean declaration
citing it, render the pair — is shared.  Node location comes from
`scripts/paper_nodes.py`, the same module the per-paper provenance checkers use, so each
citation scheme has exactly one implementation.  What differs per paper is *editorial*
and lives in `PAPERS_EDITORIAL` below plus the page prose in
`scripts/trust-surface-template.html`:

* **Logical Induction** carries a machine-checked strength classification
  (`scripts/coverage-classification.md`) and years of hand-written per-node reading
  notes, so its cards show a tier badge, a "how the panes line up" note and a
  "what to check" note.
* **Cartesian Frames** and **ModalAgents** have neither.  Their sections are a
  correspondence view: the paper node beside its Lean endpoints, carrying only what
  genuinely exists — the Cartesian Frames errata cross-references and the Claim 35
  intentional-deviation ruling; for ModalAgents, which nodes are out of scope and which
  inventoried endpoints deliberately carry no annotation.  No tier is invented for them,
  and their sections say so rather than omitting the column silently.
* **Condensation** is mid-flight, so its editorial entry names the two blocks of
  `AxiomAudit.lean` that partition its annotated surface — the `#assert_axioms_clean`
  inventory and the proof-pending staging block — and every declaration of its section is
  badged *axiom-clean* or *staged*, with the node's own verdict on the card header.  Any
  paper reaching a milestone statement-first opts into the same treatment by naming those
  two blocks; a paper that names neither renders exactly as it always has.

Run from anywhere:  python3 scripts/gen-trust-surface.py
Regenerate after any change to a paper source, a library's annotations, the registry,
the coverage table, or the template; `scripts/check_trust_surface.py` enforces this.
"""

import glob
import html
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'
sys.path.insert(0, ROOT + 'scripts')

import paper_nodes  # noqa: E402
from papers import PAPERS  # noqa: E402

import latex2mathml.converter as _l2m  # noqa: E402


def read(rel):
    return open(ROOT + rel, encoding='utf-8').read()


# ======================================================================
# Shared: LaTeX -> HTML
# ======================================================================

GREEK = {'phi':'φ','psi':'ψ','delta':'δ','epsilon':'ε','varepsilon':'ε','sigma':'σ','alpha':'α',
 'beta':'β','gamma':'γ','Gamma':'Γ','mu':'μ','nu':'ν','xi':'ξ','omega':'ω','Theta':'Θ','theta':'θ',
 'lambda':'λ','kappa':'κ','tau':'τ','rho':'ρ','pi':'π','chi':'χ','eta':'η','zeta':'ζ','iota':'ι'}
SIMPLE = {
 'nn':'n','mm':'m','deff':'f','fuz':'w','prob':'p','exf':'ξ','aff':'A','affluv':'B',
 'pt':'ℙ','BelState':'ℙ','EE':'𝔼','Expt':'𝔼','World':'𝕎','Theory':'Γ','dt':'D',
 'NN':'ℕ','QQ':'ℚ','RR':'ℝ','BB':'𝔹','ZZ':'ℤ',
 'eqsim':'≈','gtrsim':'≳','lesssim':'≲','le':'≤','leq':'≤','ge':'≥','geq':'≥','neq':'≠','ne':'≠',
 'in':'∈','notin':'∉','subseteq':'⊆','subset':'⊂','cup':'∪','cap':'∩','emptyset':'∅',
 'to':'→','rightarrow':'→','Rightarrow':'⇒','mapsto':'↦','land':'∧','lor':'∨','lnot':'¬','neg':'¬',
 'wedge':'∧','vee':'∨','forall':'∀','exists':'∃','vdash':'⊢','nvdash':'⊬','models':'⊨',
 'infty':'∞','cdot':'·','cdots':'⋯','ldots':'…','dots':'…','times':'×','pm':'±','mid':'|',
 'sum':'∑','prod':'∏','liminf':'lim inf','limsup':'lim sup','lim':'lim','sup':'sup','inf':'inf',
 'max':'max','min':'min','log':'log','circ':'∘','equiv':'≡','approx':'≈','sim':'~',
 'lfloor':'⌊','rfloor':'⌋','lceil':'⌈','rceil':'⌉','langle':'⟨','rangle':'⟩',
 'top':'⊤','bot':'⊥','implies':'⇒','iff':'⇔','setminus':'∖','quad':' ','qquad':'  ',
 'colon':':',';':' ',',':' ','!':'','ec':'e.c.','ecc':'e.c.','OneOperator':'𝟙','ind':'Ind',
 'cworlds':'𝒫𝒞','worlds':'𝒲','luvval':'𝕌','Value':'value','val':'val',
 'textbflic':'logical induction criterion','textbfli':'logical inductor','bm':'','textbf':'',
 'lic':'logical induction criterion','li':'logical inductor','Trader':'T','trading':'trading',
 'Bayesian':'Pr','textsc':'','mathbb':'','displaystyle':'','ensuremath':'','xspace':'',
}

# Logical Induction's private macro layer, expanded before the MathML conversion.
LI_MACRO_LATEX = [
 (r'\\fin(?![A-Za-z])', r'\\operatorname{Fin}'),
 (r'\\trade(?![A-Za-z])', 'T'), (r'\\cash(?![A-Za-z])', 'c'),
 (r'\\pf\[([^\]]*)\]', r'^{*\1}'), (r'\\pf(?![A-Za-z])', '^{*n}'),
 (r'\\features(?![A-Za-z])', r'\\mathcal{F}'),
 (r'\\exfeatures(?![A-Za-z])', r'\\mathcal{EF}'),
 (r'\\affconst(?![A-Za-z])', 'c'), (r'\\fconst(?![A-Za-z])', '1'),
 (r'\\feature(?![A-Za-z])', r'\\alpha'),
 (r'\\Valuation(?![A-Za-z])', r'\\mathbb{V}'),
 (r'\\seqA(?![A-Za-z])', r'\\overline{A}'), (r'\\seqB(?![A-Za-z])', r'\\overline{B}'),
 (r'\\seqw(?![A-Za-z])', r'\\overline{w}'),
 (r'\\gen\{([^{}]*)\}', r'{\1}^{gen}'), (r'\\gens(?![A-Za-z])', 'gen'),
 (r'\\thmind\[([^\]]*)\]', r'\\operatorname{Thm}_{\1}'),
 (r'\\thmind(?![A-Za-z])', r'\\operatorname{Thm}_{\\Gamma}'),
 (r'\\thmval\[([^\]]*)\]', r'\\operatorname{Val}_{\1}'),
 (r'\\thmval(?![A-Za-z])', r'\\operatorname{Val}_{\\Gamma}'),
 (r'\\LUVs(?![A-Za-z])', r'\\mathcal{U}'), (r'\\pseudo(?![A-Za-z])', 'p'),
 (r'\\varepsilons(?![A-Za-z])', r'\\overline{\\varepsilon}'),
 (r'\\ftn(?![A-Za-z])', r'(\\overline{\\mathbb{P}})'),
 (r'\\consen(?![A-Za-z])', r'\\operatorname{Con}'),
 (r'\\Oo(?![A-Za-z])', r'\\mathcal{O}'),
 (r'\\textnormal', r'\\text'),

 (r'\\mleft', r'\\left'), (r'\\mright', r'\\right'),
 (r'\\nn(?![A-Za-z])', 'n'), (r'\\mm(?![A-Za-z])', 'm'), (r'\\deff(?![A-Za-z])', 'f'), (r'\\fuz(?![A-Za-z])', 'w'),
 (r'\\probs(?![A-Za-z])', r'\\overline{p}'), (r'\\prob(?![A-Za-z])', 'p'), (r'\\exf(?![A-Za-z])', r'\\xi'),
 (r'\\affluv(?![A-Za-z])', 'B'), (r'\\aff(?![A-Za-z])', 'A'),
 (r'\\pt(?![A-Za-z])', r'\\mathbb{P}'), (r'\\BelState(?![A-Za-z])', r'\\mathbb{P}'),
 (r'\\MP(?![A-Za-z])', r'\\overline{\\mathbb{P}}'), (r'\\DP(?![A-Za-z])', r'\\overline{D}'), (r'\\dt(?![A-Za-z])', 'D'),
 (r'\\EE(?![A-Za-z])', r'\\mathbb{E}'), (r'\\Expt(?![A-Za-z])', r'\\mathbb{E}'),
 (r'\\World(?![A-Za-z])', r'\\mathbb{W}'), (r'\\Theory(?![A-Za-z])', r'\\Gamma'),
 (r'\\NN(?![A-Za-z])', r'\\mathbb{N}'), (r'\\QQ(?![A-Za-z])', r'\\mathbb{Q}'), (r'\\RR(?![A-Za-z])', r'\\mathbb{R}'),
 (r'\\BB(?![A-Za-z])', r'\\mathbb{B}'), (r'\\ZZ(?![A-Za-z])', r'\\mathbb{Z}'),
 (r'\\phis(?![A-Za-z])', r'\\overline{\\phi}'), (r'\\psis(?![A-Za-z])', r'\\overline{\\psi}'),
 (r'\\deltas(?![A-Za-z])', r'\\overline{\\delta}'),
 (r'\\seq\s*\{', r'\\overline{'), (r'\\seq\s*(\\[A-Za-z]+)', r'\\overline{\1}'),
 (r'\\enc\s*\{', r'\\underline{'), (r'\\enc\s*(\\[A-Za-z]+)', r'\\underline{\1}'),
 (r'\\ctsind\{', r'\\operatorname{Ind}_{'),
 (r'\\eqsim(?![A-Za-z])', r'\\approx'), (r'\\cworlds(?![A-Za-z])', r'\\mathcal{PC}'),
 (r'\\worlds(?![A-Za-z])', r'\\mathcal{W}'), (r'\\luvval(?![A-Za-z])', r'\\mathbb{U}'),
 (r'\\BCS\b(\[[^\]]*\])?', r'\\mathcal{BCS}(\\overline{\\mathbb{P}})'),
 (r'\\BLCS\b(\[[^\]]*\])?', r'\\mathcal{BLCS}(\\overline{\\mathbb{P}})'),
 (r'\\OneOperator(?![A-Za-z])', r'\\mathbf{1}'), (r'\\Bayesian(?![A-Za-z])', r'\\mathrm{Pr}'),
 (r'\\bm(?![A-Za-z])', r'\\mathbf'), (r'\\Trader(?![A-Za-z])', 'T'),
 (r'\\Sentences(?![A-Za-z])', r'\\mathcal{S}'), (r'\\Lang(?![A-Za-z])', r'\\mathcal{L}'),
 (r'\\marketmaker(?![A-Za-z])', r'\\operatorname{MarketMaker}'),
 (r'\\budgeter(?![A-Za-z])', r'\\operatorname{Budgeter}'),
 (r'\\tradingfirm(?![A-Za-z])', r'\\operatorname{TradingFirm}'),
 (r'\\LIA(?![A-Za-z])', r'\\operatorname{LIA}'), (r'\\any(?![A-Za-z])', r'\\cdot'),
 (r'\\ec\[\]', r'\\text{e.c.}'), (r'\\ec(?![A-Za-z])', r'\\text{e.c.}'),
 (r'\\pgenable(?![A-Za-z])', r'\\overline{\\mathbb{P}}\\text{-generable}'),
 (r'\\lic(?![A-Za-z])', r'\\text{logical induction criterion}'),
 (r'\\li(?![A-Za-z])', r'\\text{logical inductor}'),
]
LI_PRE_LATEX = [
 (r'\\seq\s*\{', r'\\overline{'),
 (r'\\seq\s*(\\[A-Za-z]+)', r'\\overline{\1}'),
 (r'\\seq\s+([A-Za-z])', r'\\overline{\1}'),
 (r'\\enc\s*\{', r'\\underline{'),
 (r'\\enc\s*(\\[A-Za-z]+)', r'\\underline{\1}'),
 (r'\\gen\s*(\\[A-Za-z]+)', r'{\1}^{\\dagger}'),
 (r'\\gen\{([^{}]*)\}', r'{\1}^{\\dagger}'),
 (r'\\gen\s+([A-Za-z])', r'{\1}^{\\dagger}'),
]

# Cartesian Frames and ModalAgents use stock LaTeX in their statements; the handful of
# operator names they write as plain words need no expansion, and anything unknown falls
# through to the same degradation path as Logical Induction's.
CF_MACRO_LATEX = [
 (r'\\Image(?![A-Za-z])', r'\\operatorname{Image}'),
 (r'\\Agent(?![A-Za-z])', r'\\operatorname{Agent}'),
 (r'\\Env(?![A-Za-z])', r'\\operatorname{Env}'),
]
MA_MACRO_LATEX = [
 (r'\\F(?![A-Za-z])', r'\\mathbb{F}'),
 (r'\\R(?![A-Za-z])', r'\\mathbb{R}'),
]


def replace_nested(s, macro, fmt):
    """Replace \\macro{...} with fmt % inner, handling one nesting level robustly."""
    out = []
    i = 0
    while True:
        j = s.find('\\' + macro + '{', i)
        if j < 0:
            out.append(s[i:]); break
        out.append(s[i:j])
        k = j + len(macro) + 2
        depth = 1
        while k < len(s) and depth:
            if s[k] == '{': depth += 1
            elif s[k] == '}': depth -= 1
            k += 1
        inner = s[j + len(macro) + 2 : k - 1]
        out.append(fmt % inner if '%s' in fmt else fmt)
        i = k
    return ''.join(out)


def texmath(s):
    s = s.replace('\\{', '&#123;').replace('\\}', '&#125;')
    # structural first
    s = re.sub(r'\\(?:left|right|mleft|mright|big|Big|bigg|Bigg)\s*', '', s)
    s = re.sub(r'\\(?:text|textrm|mathrm|operatorname|small)\s*\{([^{}]*)\}', r'\1', s)
    s = re.sub(r'\\mathcal\{P\\-C\}', '𝒫𝒞', s)
    s = re.sub(r'\\mathcal\{B\\-C\\-S\}', 'ℬ𝒞𝒮', s)
    s = re.sub(r'\\mathcal\{B\\-L\\-C\\-S\}', 'ℬℒ𝒞𝒮', s)
    s = replace_nested(s, 'quot', '\u201c%s\u201d')
    s = replace_nested(s, 'enc', '<span class="enc">%s</span>')
    s = replace_nested(s, 'seq', '<span class="ov">%s</span>')
    # composite macros
    for _ in range(6):
        s = re.sub(r'\\seq\{([^{}]*)\}', r'<span class="ov">\1</span>', s)
        s = re.sub(r'\\enc\{([^{}]*)\}', r'<span class="enc">\1</span>', s)
        s = re.sub(r'\\quot\{([^{}]*)\}', r'“\1”', s)
        s = re.sub(r'\\ctsind\{([^{}]*)\}', r'Ind<sub>\1</sub>', s)
        s = re.sub(r'\\frac\{([^{}]*)\}\{([^{}]*)\}', r'(\1)/(\2)', s)
        s = re.sub(r'\\BCS(?:\[[^\]]*\])?', 'ℬ𝒞𝒮(ℙ‾)', s)
        s = re.sub(r'\\BLCS(?:\[[^\]]*\])?', 'ℬℒ𝒞𝒮(ℙ‾)', s)
    s = s.replace('\\MP', '<span class="ov">ℙ</span>')
    s = s.replace('\\DP', '<span class="ov">D</span>')
    s = s.replace('\\phis', '<span class="ov">φ</span>')
    s = s.replace('\\psis', '<span class="ov">ψ</span>')
    s = s.replace('\\deltas', '<span class="ov">δ</span>')
    s = s.replace('\\probs', '<span class="ov">p</span>')
    s = s.replace('\\pgenable', 'ℙ‾-generable')
    # greek + simple
    def repl(m):
        w = m.group(1)
        if w in GREEK: return GREEK[w]
        if w in SIMPLE: return SIMPLE[w]
        return w  # unknown macro: drop backslash, keep word
    s = re.sub(r'\\([A-Za-z]+)', repl, s)
    # subscripts / superscripts
    for _ in range(4):
        s = re.sub(r'_\{([^{}]*)\}', r'<sub>\1</sub>', s)
        s = re.sub(r'\^\{([^{}]*)\}', r'<sup>\1</sup>', s)
    s = re.sub(r'_([A-Za-z0-9φψδεσνξω∞]|𝟙)', r'<sub>\1</sub>', s)
    s = re.sub(r'\^([A-Za-z0-9φψ])', r'<sup>\1</sup>', s)
    s = s.replace('{','').replace('}','')
    s = re.sub(r'\s+', ' ', s)
    return s.strip()


def unescape_html(x):
    return x.replace('&lt;','<').replace('&gt;','>').replace('&amp;','&')


class TexRenderer:
    """Convert one paper's statement TeX to self-contained HTML + MathML.

    The conversion pipeline is shared; `macros` and `pre_macros` are the paper's own
    private macro layer, expanded before handing the segment to latex2mathml.  Anything
    still unrecognised degrades to the `texmath` glyph substitution rather than being
    dropped, so an unconverted formula is visibly approximate instead of silently absent.
    """

    # Environments with no honest HTML/MathML rendering.  A commutative diagram degraded
    # to glyph soup would misrepresent the paper, so the card marks the gap instead.
    UNRENDERABLE = re.compile(
        r'(?:\\\[\s*)?\\begin\{(tikzcd|tikzpicture|blockarray)\}.*?\\end\{\1\}(?:\s*\\\])?',
        re.S)
    DIAGRAM_SENTINEL = '@@UNRENDERABLE@@'

    def __init__(self, macros, pre_macros=()):
        self.macros = list(macros)
        self.pre_macros = list(pre_macros)
        self.failures = []
        self.omitted = []

    def expand_latex(self, seg):
        for _ in range(3):
            for pat, rep in self.pre_macros:
                seg = re.sub(pat, rep, seg)
        for pat, rep in self.macros:
            if re.fullmatch(r'[A-Za-z0-9]+', rep):
                rep = '{' + rep + '}'
            seg = re.sub(pat, rep, seg)
        return seg

    def tex2mml(self, seg, display=False):
        seg = replace_nested(seg, 'quot', '\\text{\u201c}%s\\text{\u201d}')
        seg = replace_nested(seg, 'proofin', '')
        seg = self.expand_latex(seg)
        try:
            return _l2m.convert(seg, display='block' if display else 'inline')
        except Exception:
            self.failures.append(seg.strip()[:120])
            h = texmath(seg.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;'))
            cls = 'dm' if display else 'im'
            return '<span class="%s">%s</span>' % (cls, h)

    def block(self, s, label=None):
        """Full statement body -> html (handles \\[ \\], $..$, itemize, text macros)."""
        def mark(m):
            self.omitted.append((label, m.group(1)))
            return '\n\n%s\n\n' % self.DIAGRAM_SENTINEL
        s = self.UNRENDERABLE.sub(mark, s)
        # Footnotes are the paper's own text; keep them, parenthesised in place.
        s = s.replace('\\footnotemark', '')
        for macro in ('footnotetext', 'footnote'):
            s = replace_nested(s, macro, ' (footnote: %s)')
        s = replace_nested(s, 'proofin', '')
        # Layout-only wrappers, and display-math environments spelled the long way.
        s = re.sub(r'\\(?:begin|end)\{center\}', '', s)
        s = re.sub(r'\\begin\{(?:displaymath|equation\*?)\}', r'\\[', s)
        s = re.sub(r'\\end\{(?:displaymath|equation\*?)\}', r'\\]', s)
        s = re.sub(r'%[^\n]*', '', s)
        s = re.sub(r'\\(?:noindent|smallskip|medskip|bigskip|par)\b', '', s)
        s = replace_nested(s, 'proofin', '')
        # protect html
        s = s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        # split display math
        parts = re.split(r'\\\[|\\\]', s)
        htmlparts = []
        for k, part in enumerate(parts):
            if k % 2 == 1:
                htmlparts.append('<div class="dmath">%s</div>'
                                 % self.tex2mml(unescape_html(part), display=True))
            else:
                # inline math
                segs = re.split(r'\$', part)
                buf = []
                for j, seg in enumerate(segs):
                    if j % 2 == 1:
                        buf.append(self.tex2mml(unescape_html(seg)))
                    else:
                        t = seg
                        t = re.sub(r'\\emph\{([^{}]*)\}', r'<em>\1</em>', t)
                        t = re.sub(r'\\textbf\{([^{}]*)\}', r'<strong>\1</strong>', t)
                        t = re.sub(r'\\textit\{([^{}]*)\}', r'<em>\1</em>', t)
                        # Prose font switches carry no meaning here; keep the words.
                        t = re.sub(r'\\(?:texttt|textsf|textrm|textnormal|mathsf|mathrm'
                                   r'|text)\{([^{}]*)\}', r'\1', t)
                        t = re.sub(r'\\ref\{[^{}]*\}', '[ref]', t)
                        t = re.sub(r'\\(?:cref|Cref|eqref)\{[^{}]*\}', '[ref]', t)
                        t = t.replace('\\ec[]', 'e.c.').replace('\\ec', 'e.c.')
                        t = t.replace('\\pgenable', 'ℙ‾-generable')
                        # List environments, with or without an options argument.
                        t = re.sub(r'\\begin\{itemize\}(?:\[[^\]]*\])?', '<ul>', t)
                        t = t.replace('\\end{itemize}', '</ul>')
                        t = re.sub(r'\\begin\{enumerate\}(?:\[[^\]]*\])?', '<ol>', t)
                        t = t.replace('\\end{enumerate}', '</ol>')
                        t = re.sub(r'\\item\s*', '</li-mark><li>', t)
                        t = t.replace('``', '“').replace("''", '”')
                        t = re.sub(r'\\([A-Za-z]+)', lambda m: SIMPLE.get(m.group(1), GREEK.get(m.group(1), m.group(1))), t)
                        t = t.replace('{','').replace('}','').replace('~',' ')
                        buf.append(t)
                htmlparts.append(''.join(buf))
        res = ''.join(htmlparts)
        # fix list item marks
        res = re.sub(r'&lt;ul&gt;', '<ul>', res)
        res = res.replace('<ul></li-mark>', '<ul>').replace('</li-mark>', '')
        # paragraphs
        paras = [p.strip() for p in res.split('\n\n') if p.strip()]
        out = '\n'.join('<p>%s</p>' % p if not p.startswith('<div') and not p.startswith('<ul') else p
                        for p in paras)
        return out.replace(
            '<p>%s</p>' % self.DIAGRAM_SENTINEL,
            '<p class="omitted">[the paper prints a diagram here; it has no faithful '
            'text rendering — see the arXiv PDF]</p>').replace(
            self.DIAGRAM_SENTINEL,
            '[diagram — see the arXiv PDF]')


ACCENTS = {'"a':'ä','"o':'ö','"u':'ü','"e':'ë','\'e':'é','\'a':'á','\'o':'ó','`e':'è',
           '`a':'à','^e':'ê','^o':'ô','~n':'ñ','cc':'ç','va':'ǎ','vs':'š'}


def clean_title(t):
    """A node's bracketed title as plain text: the papers write TeX in there."""
    if not t:
        return ''
    t = re.sub(r'\\(["\'`^~cv])\s*\{?([A-Za-z])\}?',
               lambda m: ACCENTS.get(m.group(1) + m.group(2), m.group(2)), t)
    for _ in range(3):
        t = re.sub(r'\\(?:textsf|texttt|textbf|textit|textrm|emph|mathsf|mathrm|text)'
                   r'\{([^{}]*)\}', r'\1', t)
    def inline_math(m):
        # Titles are plain text, so the overline/underline spans become their glyphs.
        s = texmath(m.group(1))
        s = re.sub(r'<span class="ov">([^<]*)</span>', r'\1‾', s)
        s = re.sub(r'<span class="enc">([^<]*)</span>', r'⌜\1⌝', s)
        return re.sub(r'<[^>]+>', '', s)
    t = re.sub(r'\$([^$]*)\$', inline_math, t)
    t = re.sub(r'\\([A-Za-z]+)',
               lambda m: SIMPLE.get(m.group(1), GREEK.get(m.group(1), m.group(1))), t)
    return t.replace('{', '').replace('}', '').strip()


class ExtractionRenderer:
    """Render a statement that was read off a `pdftotext -layout` extraction.

    Condensation has no TeX source (see `scripts/papers.py`), so there is no markup to
    convert: what is committed is the printed page as plain text, with its own line
    breaks, column alignment and inline display equations.  Reflowing that into prose
    would silently rewrite the paper's statement, and glyph-substituting it would claim a
    conversion that never happened — so it is shown *verbatim*, in a preformatted block,
    with only HTML escaping applied.

    Its interface matches `TexRenderer`'s so `build_correspondence` need not branch, and
    its `failures`/`omitted` are permanently empty: nothing is approximated here, so
    there is nothing to warn about.
    """

    def __init__(self):
        self.failures = []
        self.omitted = []

    def block(self, s, label=None):
        return '<pre class="extract">%s</pre>' % html.escape(s)


def renderer_warnings(key, renderer):
    """What a paper's conversion could not render, named so it can be checked by hand."""
    out = ['%s: %s prints a %s the converter has no faithful rendering for — the card '
           'marks the gap and points at the PDF rather than approximating it'
           % (key, label or '(unlabelled node)', env)
           for label, env in renderer.omitted]
    out += ['%s: formula fell back to glyph substitution — %s' % (key, f)
            for f in renderer.failures]
    return out


def md_inline(s):
    s = html.escape(s)
    s = re.sub(r'`([^`]*)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'(?<![*\w])\*([^*\n]+)\*(?![*\w])', r'<em>\1</em>', s)
    return s


# ======================================================================
# Shared: Lean declaration extraction
# ======================================================================

DECL_PAT = re.compile(
    r'^\s*(?:private\s+)?(?:noncomputable\s+)?'
    r'(theorem|lemma|def|structure|class|abbrev)\s+([\w.\x27]+)')


class LeanLibrary:
    """The `.lean` sources of one library, with statement-level extraction."""

    def __init__(self, lib):
        self.files = {f: open(f, encoding='utf-8').read().split('\n')
                      for f in glob.glob(ROOT + lib + '/**/*.lean', recursive=True)}
        root_module = ROOT + lib + '.lean'
        if os.path.exists(root_module):
            self.files.setdefault(root_module,
                                  open(root_module, encoding='utf-8').read().split('\n'))

    def find_decl(self, name):
        """Locate a declaration by (possibly unqualified) name; dotted match wins."""
        short = name.split('.')[-1]
        best = (None, None)
        for f, ls in self.files.items():
            for idx, l in enumerate(ls):
                m = DECL_PAT.match(l)
                if not m: continue
                written = m.group(2)
                if written == name or name.endswith('.' + written):
                    return f, idx     # exact dotted match wins immediately
                if written == short or written.endswith('.' + short):
                    if best[0] is None:
                        best = (f, idx)
        return best

    def extract_at(self, f, idx):
        """Statement + docstring of the declaration starting at 0-based line `idx`."""
        ls = self.files[f]
        # docstring: scan back
        doc = ''
        j = idx - 1
        # skip attribute/open/set_option lines
        while j >= 0 and (ls[j].strip().startswith(('attribute','set_option','open','@['))
                          or ls[j].strip() == ''):
            j -= 1
        if j >= 0 and ls[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and '/--' not in ls[k]:
                k -= 1
            doc = '\n'.join(ls[k:j+1])
            doc = doc.strip().removeprefix('/--').removesuffix('-/').strip()
        # signature: from idx forward until a line contains ':=' (cut there) or 'where'
        is_struct = bool(re.match(r'\s*(?:private\s+)?(?:noncomputable\s+)?(structure|class)\b', ls[idx]))
        sig_lines = []
        if is_struct:
            seen_where = False
            for l in ls[idx:idx+80]:
                if seen_where and l.strip() == '':
                    break
                if re.search(r'\bwhere\s*$', l):
                    seen_where = True
                sig_lines.append(l.rstrip())
            sig = '\n'.join(sig_lines).rstrip()
        else:
            for l in ls[idx:idx+80]:
                if ':=' in l:
                    cut = l[:l.index(':=')].rstrip()
                    if cut: sig_lines.append(cut)
                    break
                if re.search(r'\bwhere\s*$', l):
                    sig_lines.append(re.sub(r'\bwhere\s*$','',l).rstrip())
                    break
                sig_lines.append(l.rstrip())
            sig = '\n'.join(sig_lines).rstrip()
        labels = (re.findall(r'`([\w:]+)`', re.search(r'Paper node:(.*)', doc).group(1))
                  if 'Paper node:' in doc else [])
        return {'file': f.replace(ROOT, ''), 'sig': sig, 'labels': labels, 'doc': doc}

    def extract(self, name):
        f, idx = self.find_decl(name)
        if f is None:
            return None
        e = self.extract_at(f, idx)
        e['name'] = name
        return e


def audit_inventory_names(audit_src):
    """Every identifier listed under an `#assert_axioms_clean` command, in order."""
    src = re.sub(r'/-.*?-/', '', audit_src, flags=re.S)
    names = []
    lines = src.split('\n'); i = 0
    while i < len(lines):
        m = re.match(r'\s*#assert_axioms_clean(_except)?\s*(.*)', lines[i])
        if m:
            block = [m.group(2)]; i += 1
            while i < len(lines):
                s = lines[i].strip()
                if s == '' or s[0] in '#-/' or s.startswith('open'): break
                block.append(s); i += 1
            for b in block:
                names += re.findall(r'[A-Za-z_][\w.]*', b)
            continue
        i += 1
    return [n for n in dict.fromkeys(names)]


# ======================================================================
# Shared: card / nav rendering
# ======================================================================

CARD = '''
<article class="node" id="%(anchor)s">
  <header class="node-head">
    <label class="check"><input type="checkbox" data-node="%(anchor)s" aria-label="mark %(lab)s read"></label>
    <span class="node-label">%(lab)s</span>
    <span class="node-title">%(title)s</span>
    %(badge)s
  </header>
  <div class="panes">
    <section class="paper-pane">
      <div class="pane-tag">Paper · %(source)s</div>
      %(paper)s
    </section>
    <section class="lean-pane">
      <div class="pane-tag">Lean · statement only (proof body is kernel-checked)</div>
      %(sig)s
    </section>
  </div>%(notes)s
</article>'''


def endpoint_pane(endpoints, staging=None):
    """The Lean pane's slide deck: one statement per inventory endpoint.

    `staging`, for a paper that stages proof-pending endpoints (see `Staging`), badges
    each declaration axiom-clean or staged.  A paper that stages nothing passes `None`
    and its pane renders exactly as before.
    """
    slides = ''
    for i, (name, e) in enumerate(endpoints):
        slides += ('<div class="ep-slide%s"><div class="ep-head">'
                   '<code class="ep-name">%s</code>%s<span class="ep-file">%s</span></div>'
                   '<pre class="sig">%s</pre></div>') % (
            '' if i == 0 else ' hidden', html.escape(name),
            '' if staging is None else staging.badge(name), html.escape(e['file']),
            html.escape(e['sig']))
    controls = ''
    if len(endpoints) > 1:
        controls = ('<div class="ep-nav"><button class="ep-prev" aria-label="previous endpoint">&#8249;</button>'
                    '<span class="ep-count" data-total="%d">1 / %d</span>'
                    '<button class="ep-next" aria-label="next endpoint">&#8250;</button>'
                    '<span class="ep-nav-hint">inventory endpoints for this node</span></div>') % (
            len(endpoints), len(endpoints))
    return controls + slides


def render_card(*, anchor, lab, title, badge, source, paper_html, endpoints, notes,
                staging=None):
    return CARD % dict(anchor=anchor, lab=lab, title=html.escape(clean_title(title)),
                       badge=badge,
                       source=source, paper=paper_html,
                       sig=endpoint_pane(endpoints, staging),
                       notes=''.join('\n' + n for n in notes))


def note(cls, tag, body_html):
    return ('  <div class="%s"><span class="%s-tag">%s</span> %s</div>'
            % (cls, cls.removesuffix('-note'), tag, body_html))


def audit_footer(tag, body_html):
    return ('  <footer class="audit-note"><span class="audit-tag">%s</span> %s</footer>'
            % (tag, body_html))


def inventory_names(block, warnings):
    """The declaration names `block`'s `#assert_axioms_clean` gate checks.

    `paper_nodes.read_inventory` returns an `Inventory` (names plus ready-to-print
    problems); a bare set is accepted too, so this generator does not break in either
    direction while that module's shape settles.  Problems are surfaced as page
    warnings rather than absorbed: a token the parser cannot account for is exactly the
    way the gate would be silently disarmed.
    """
    parsed = paper_nodes.read_inventory(ROOT + 'AxiomAudit.lean', block)
    if parsed is None:
        return set()
    warnings += list(getattr(parsed, 'problems', None) or ())
    return set(getattr(parsed, 'names', parsed))


class Staging:
    """Which of a paper's declarations are proved, and which only have a statement.

    A paper still in flight splits its annotated surface across two blocks of
    `AxiomAudit.lean`: the inventory block is the `#assert_axioms_clean` gate, and the
    pending block is *pure comment* naming every annotated endpoint whose proof is still
    `sorry`, plus — in its `SECTION: consumers` half — un-annotated declarations that
    consume one.  Rendering both alike would show a `sorry` as a proof, so every
    declaration of such a paper carries its state as a badge and every card its verdict.

    A paper that declares no `pending_block` in `PAPERS_EDITORIAL` has no `Staging` at
    all and renders exactly as it did before this existed.
    """

    def __init__(self, key, lib, pending_block, inventory_block, staged, consumers,
                 inventory):
        self.key = key
        self.lib = lib
        self.pending_block = pending_block
        self.inventory_block = inventory_block
        self.n_staged = len(staged)
        self.n_consumers = len(consumers)
        self.staged = {}
        for table in (staged, consumers):
            for name, reason in table.items():
                for form in self.forms(name):
                    self.staged[form] = reason
        self.inventory = {form for name in inventory for form in self.forms(name)}

    def forms(self, name):
        """The qualified names a block entry may resolve to — bare, or under the root."""
        return {name, '%s.%s' % (self.lib, name)}

    def state(self, name):
        """`'staged'`, `'proved'`, or `None` when the name is in neither block."""
        if name in self.staged:
            return 'staged'
        if name in self.inventory:
            return 'proved'
        return None

    def badge(self, name):
        """The per-declaration badge shown beside its name in the Lean pane."""
        state = self.state(name)
        if state == 'staged':
            return ('<span class="staged" title="%s">staged &middot; sorry</span>'
                    % html.escape(self.staged[name], quote=True))
        if state == 'proved':
            return '<span class="staged proved">axiom-clean</span>'
        return ''

    def node_badge(self, names):
        """The card header's verdict over all the declarations carrying one node."""
        states = [self.state(n) for n in names]
        if not states or None in states:
            return ''
        if all(s == 'staged' for s in states):
            return '<span class="staged">proof staged</span>'
        if any(s == 'staged' for s in states):
            return '<span class="staged">partly staged</span>'
        return '<span class="staged proved">axiom-clean</span>'

    def dot(self, names):
        """The left rail's dot class, so a staged node is visible without scrolling."""
        return 'staged' if any(self.state(n) == 'staged' for n in names) else 'plain'

    def note(self, names):
        """A card footer naming what each staged declaration is still waiting on."""
        rows = [n for n in names if self.state(n) == 'staged']
        if not rows:
            return []
        body = '; '.join('<code>%s</code> — %s'
                         % (html.escape(n), md_inline(self.staged[n])) for n in rows)
        return [audit_footer('Proof staged — not axiom-checked', body)]

    def counts(self, names):
        """(proved, staged) over the distinct declarations rendered in the section."""
        states = [self.state(n) for n in set(names)]
        return states.count('proved'), states.count('staged')

    def legend(self, names):
        """The section's legend: what each badge means, with this build's counts."""
        proved, staged = self.counts(names)
        consumers = ''
        if self.n_consumers:
            consumers = (
                ' A further %d declaration%s carr%s no <code>Paper node:</code> '
                'annotation but consume%s a staged result, and are listed in the same '
                'block\u2019s consumers section.'
                % (self.n_consumers, '' if self.n_consumers == 1 else 's',
                   'ies' if self.n_consumers == 1 else 'y',
                   's' if self.n_consumers == 1 else ''))
        return (
            '<div class="method">\n'
            '<h3>Proved and staged endpoints</h3>\n'
            '<div class="legend"><span class="staged proved">axiom-clean</span>'
            '<span class="count">%d — listed in <code>AxiomAudit.lean</code>\u2019s '
            '<code>%s</code> block, so <code>#assert_axioms_clean</code> has checked that '
            'the proof depends on no <code>sorry</code> and no added axiom.</span></div>\n'
            '<div class="legend"><span class="staged">staged &middot; sorry</span>'
            '<span class="count">%d — the <em>statement</em> is final, the proof is not: '
            'staged in the <code>%s</code> block, which is pure comment and asserts '
            'nothing. Each card\u2019s footer names what it waits on.%s</span></div>\n'
            '<p>Every declaration below carries one of these two badges, and each card\u2019s '
            'header carries the node\u2019s own verdict — <em>axiom-clean</em>, '
            '<em>partly staged</em> (some carrier of that node is proved and some is not), '
            'or <em>proof staged</em>. A staged endpoint is a claim about the statement '
            'only; nothing badged staged is claimed proved.</p>\n'
            '</div>'
            % (proved, html.escape(self.inventory_block), staged,
               html.escape(self.pending_block), consumers))


def staging_for(key, paper, warnings):
    """The paper's `Staging`, or `None` when it stages no proof-pending endpoints.

    Driven entirely by `PAPERS_EDITORIAL[key]`: a paper opts in by naming its
    `pending_block` (and the `inventory_block` its proved endpoints are gated by), so a
    second paper reaching statement-first for a milestone gets the same treatment by
    adding two keys, and every other paper keeps rendering as it always has.
    """
    conf = PAPERS_EDITORIAL[key]
    block = conf.get('pending_block')
    if not block:
        return None
    audit = ROOT + 'AxiomAudit.lean'
    pending = paper_nodes.read_pending(audit, block)
    if pending is None:
        warnings.append('%s: %s names no %s-BEGIN/END block in AxiomAudit.lean, so no '
                        'endpoint could be marked staged' % (key, 'PAPERS_EDITORIAL', block))
        return None
    warnings += list(pending.problems)
    inventory_block = conf.get('inventory_block')
    inventory = inventory_names(inventory_block, warnings) if inventory_block else set()
    return Staging(key, paper['library'], block, inventory_block or '(none)',
                   dict(pending.entries), dict(getattr(pending, 'consumers', None) or {}),
                   inventory)


def section_titles(tex, pattern, appendix=False):
    """(position, rendered title) for each sectioning command, in source order.

    With `appendix=True` the sections after the source's `\\appendix` are relettered the
    way the paper prints them, so a card's heading matches the citation an annotation
    carries (`Claim 46 (App. B)`).
    """
    out = []
    appendix_at = tex.find('\\appendix') if appendix else -1
    letters = 0
    for m in re.finditer(pattern, tex):
        raw = m.group(2)
        t = re.sub(r'\\texorpdfstring\{[^{}]*(?:\{[^{}]*\})?[^{}]*\}\{([^}]*)\}', r'\1', raw)
        t = re.sub(r'\\label\{[^}]*\}', '', t)
        t = t.replace('\\LICtitle', 'Logical Induction Criterion').replace('\\LItitle', 'Logical Inductor')
        t = t.replace('\\LIA', 'LIA').replace('\\TradingFirm', 'Trading Firm')
        t = re.sub(r'\\emph\{([^}]*)\}', r'\1', t)
        t = re.sub(r'\$([^$]*)\$', r'\1', t)
        t = re.sub(r'\\[A-Za-z]+ ?', '', t)
        t = t.replace('{','').replace('}','').strip()
        if appendix_at >= 0 and m.start() > appendix_at and m.group(1) == 'section':
            letters += 1
            t = 'Appendix %s — %s' % (chr(ord('A') + letters - 1), t)
        out.append((m.start(), t or 'Front matter'))
    return out


def section_of(sections, position):
    best = 'Front matter'
    for p, t in sections:
        if p < position: best = t
        else: break
    return best


def group_by_section(nodes, sections):
    """[(section title, [node, …])] in source order."""
    groups = []
    for n in sorted(nodes, key=lambda n: n.position):
        sec = section_of(sections, n.position)
        if not groups or groups[-1][0] != sec:
            groups.append((sec, []))
        groups[-1][1].append(n)
    return groups


# ======================================================================
# Per-paper editorial data
# ======================================================================

# Logical Induction only.  Nodes whose strongest carriers are not reachable by the
# label index (definitions realised as structures/classes named for the concept).
LI_MANUAL = {
 'def:affcomsen': ['AffineCombination'],
 'def:bap': ['AffineCombination.BoundedCombinationSequence'],
 'def:blcp': ['LUVCombination.BoundedSequence'],
 'def:dedproc': ['DeductiveProcess', 'DeductiveProcessComputation'],
 'def:deferralfunc': ['DeferralFunction'],
 'def:fuz': ['PGenerableWeighting'],
 'def:lic': ['IsLogicalInductor'],
 'def:trader': ['Trader'],
 'def:tradestrat': ['Strategy'],
 'def:luv': ['LUV', 'PaperLUV'],
 'def:ece': ['GeneratedRatFeature'],
 'def:ec': ['EfficientlyComputable'],
 'def:lia': ['liaStates'],
}

# Curated primary endpoints (first shown with full signature).
LI_PRIMARY = {
 'def:lic':['IsLogicalInductor'],'def:ec':['EfficientlyComputable'],'def:trader':['Trader'],
 'def:tradestrat':['Strategy'],'def:affcomsen':['AffineCombination'],
 'def:bap':['AffineCombination.BoundedCombinationSequence'],'def:dedproc':['DeductiveProcess','DeductiveProcessComputation'],
 'def:deferralfunc':['DeferralFunction'],'def:ece':['GeneratedRatFeature'],'def:fuz':['PGenerableWeighting'],
 'def:luv':['LUV'],'def:blcp':['LUVCombination.BoundedSequence'],'def:lia':['liaStates'],
 'thm:li':['exists_computable_beliefSequence_logical_inductor'],
 'thm:lia':['LIA_is_logical_inductor'],'lem:tfdom':['trading_firm_dominance'],
 'thm:con':['lic_price_convergesTo'],'thm:lc':['lic_limitCoherence'],
 'thm:provind':['lic_provind'],'thm:tbo':['lic_preemptive_learning'],
 'thm:perkno':['lic_persistence_of_knowledge'],
 'thm:nd':['lic_nonDogmatism','lic_nonDogmatism_dual'],
 'thm:obu':['lic_uniform_nonDogmatism_ofCE','lic_uniform_nonDogmatism'],
 'thm:ob':['UPrefix.lic_occamBounds_ofUniversalPrefix'],
 'thm:dus':['lic_domination_universalSemimeasure_ofIndependentAtoms'],
 'thm:strict':['lic_strict_domination_universalSemimeasure_ofAtomCodes'],
 'thm:scon':['lic_conditioned_fixed_unconditional','lic_conditioned_growing_unconditional'],
 'thm:ifp':['lic_iff_of_finitePerturbation'],
 'thm:lex':['lic_learning_exclusive_exhaustive'],
 'thm:benford':['lic_learning_pseudorandom_frequency'],
 'thm:prand':['lic_learning_varied_pseudorandom'],
 'thm:prandaff':['AffineCombination.BoundedCombinationSequence.prandaff'],
 'thm:recunbiasedaff':['AffineCombination.BoundedCombinationSequence.recunbiasedaff'],
 'thm:recurringunbiasedness':['AffineCombination.recurringunbiasedness'],
 'thm:simcal':['AffineCombination.simcal'],
 'thm:wub':['lic_wub_ofComputation_unconditional'],
 'thm:wubaff':['lic_wubaff_ofComputation_unconditional'],
 'thm:affcoh':['AffineCombination.PolySequence.affcoh'],
 'thm:affpolymax':['AffineCombination.BoundedCombinationSequence.affpolymax'],
 'thm:peraffkno':['AffineCombination.PolySequence.peraffkno'],
 'thm:affprovind':['AffineCombination.PolySequence.affine_provind_theory_eq'],
 'thm:ec':['LUV.expect_converges'],'thm:ei':['lic_expectation_indicator'],
 'thm:loe':['lic_linearity_of_expectation_seq'],
 'thm:expprovind':['lic_expect_combination_provind_ge'],
 'lem:mesh':['LUVCombination.BoundedSequence.mesh_independence_ofSyntax'],
 'thm:exppolymax':['LUVCombination.BoundedSequence.exppolymax_ofSyntax'],
 'thm:expcoh':['LUVCombination.BoundedSequence.expcoh_ofSyntax'],
 'thm:perexpkno':['LUVCombination.BoundedSequence.perexpkno_ofSyntax'],
 'thm:wubexp':['luv_wubexp_ofComputation_unconditional'],
 'thm:epr':['lic_expectations_of_probabilities_closed'],
 'thm:er':['lic_iterated_expectations_closed'],
 'thm:ceu':['lic_no_expected_net_update_closed'],
 'thm:cee':['lic_expected_future_expectations_closed'],
 'thm:ccee':['lic_no_expected_net_update_conditional_closed_exact'],
 'thm:ref':['lic_introspection_closed'],
 'thm:lp':['lic_paradox_resistance_ofDiagonal_unconditional'],
 'thm:st':['lic_self_trust_closed'],
 'thm:halts':['lia_learns_halting_patterns_unconditional'],
 'thm:loops':['lic_learns_provable_nonhalting_patterns_unconditional'],
 'thm:incons':['lic_disbelief_inconsistent_theories_unconditional'],
 'thm:pac':['lic_belief_finitistic_consistency_unconditional'],
 'thm:pazfc':['lic_belief_stronger_theory_consistency_unconditional'],
 'thm:dontwait':['lic_does_not_anticipate_halting_unconditional'],
}

# Per-node correspondence notes: how the two panes line up. These complement the
# shared-vocabulary legend in the template (which covers the recurring conventions:
# hworld, Rpn*/Poly* codes, generability, the asymptotic operators, completed worlds).
LI_READING = {
 'def:lic': "The class bundles the criterion (`noExploit`, quantified over `EfficientlyComputable` traders) with two facts the paper leaves ambient: the market and the process are computable. `P n \u03c6` is the paper's \u2119\u2099(\u03c6).",
 'def:ec': "The paper's \u201ccomputable in O(poly(n))\u201d is rendered as `MachineEfficientTrader`: some `Complexity.FP` function of the unary day emits the day-n strategy's serialized symbol stream. The fuel-clocked `EfficientlyComputable` is the certification device that feeds it \u2014 `EfficientlyComputable.toMachine` compiles an `evaln` certificate into a real polynomial-time machine \u2014 and is no longer a substitution for the class.",
 'def:dedproc': "`D` and `mono` are the paper's nondecreasing finite sets; the paper's \u201ccomputably enumerable\u201d lives in the separate certificate `DeductiveProcessComputation`, taken as a hypothesis exactly where the paper says \u2018computable deductive process\u2019.",
 'def:trader': "A trader is its day-indexed strategy function; all economic content (holdings, exploitation) is derived, matching the paper's reading of a trader as a strategy sequence.",
 'def:tradestrat': "`trades` is the affine combination (the paper's \u03be\u2081\u03c6\u2081+\u2026); `rank_le` is the paper's rank condition \u2014 an n-strategy mentions only prices of days \u2264 n.",
 'def:affcomsen': "`const` + `terms` = the paper's c + \u03a3 \u03be\u1d62\u03c6\u1d62, with features as `EF` expression trees so that generability is syntactic.",
 'def:bap': "Two fields for the paper's two clauses: `poly` is the e.c. certificate on the combination sequence, `bounded` the single uniform \u2113\u00b9 bound.",
 'def:deferralfunc': "`lt` is f(n) > n; `fueled` renders \u201cf computable in time polynomial in f(n)\u201d as a poly clock in the *output*, exactly as the paper demands (so f may grow fast).",
 'def:ece': "`GeneratedRatFeature` is \u2018\u2119\u203e-generable\u2019: a rank-bounded, polynomially emitted expression whose denotation against the market's own prices is the sequence. Compare clause by clause \u2014 nothing about the values themselves is assumed.",
 'def:fuz': "Same data as `def:ece` minus the denotation clause: the weighting enters as expressions, so a trader can trade on it without knowing its values.",
 'def:luv': "The paper's LUV is a first-order formula free in one variable, and `PaperLUV` is that object literally: an `ArithmeticSemisentence 1` carrying object-level `T`-proofs of unique existence and `[0,1]` membership. `toLUV` compiles it into the abstract threshold carrier `LUV` (field `gt`) that downstream results consume; `PCWorld.ValuesAt` is *derived* through `paperTheoryDP` and the rational cut rather than assumed, and `PaperLUVSeq` compiles the literal threshold syntax to `RpnThresholdCodeSeq`. Inhabited by a varying `1/(n+1)` family. The object-level value is named by a numerator/positive-denominator pair code.",
 'def:blcp': "`poly` says the compiled threshold mesh of the combination sequence is e.c.; `bounded` is the uniform \u2113\u00b9 bound \u2014 the paper's two clauses for \u2130\u2131-progressions in \u2112\u00b9.",
 'def:lia': "Compare the recursion's *shape*: day n is the market maker's fixed point against the trading firm run on the history so far. The three components are separate audited constructions; `thm:lia` certifies the assembly.",
 'thm:li': "The conjunction mirrors def:belseq: one program emits the day-n finite association list (`code` clause), supports are finite, quotes are rational in [0,1], and the induced valuation satisfies the criterion.",
 'thm:lia': "One hypothesis \u2014 the deductive process is computable \u2014 and the conclusion instantiates the criterion at the constructed market `liaHistory DP`. This is the paper's main theorem in its constructive form.",
 'lem:tfdom': "No inductor hypothesis: any rational [0,1]-market (`hP`, with `Q`/`hQ` naming its rational quotes) exploited by *some* e.c. trader is exploited by the firm. The enumeration covering the whole class is `exists_enumeratedTrader_eq`.",
 'thm:con': "The oscillation trader is constructed inside the proof; the statement carries only the criterion instance and stage consistency. The paper's \u2018the limit exists\u2019 is the explicit `ConvergesTo`.",
 'thm:lc': "The measure \u03bc plays the paper's Pr: it is a genuine probability measure on completed worlds, agrees with the limiting belief on every sentence event, and is supported (a.e.) on worlds consistent with \u0393.",
 'thm:provind': "\u2018Sequence of theorems\u2019 becomes `hthm : \u2200 n, \u2203 k, \u03c6 n \u2208 DP.D k` \u2014 each \u03c6\u2099 eventually appears in the process \u2014 and dually for the disprovable \u03c8\u2099. Both halves of the paper's statement are one theorem here.",
 'thm:tbo': "The sSup/sInf over `fun j => P (n + j) (\u03c6 n)` are the paper's sup/inf over m \u2265 n of \u2119\u2098(\u03c6\u2099); the conclusion is the same pair of liminf/limsup identities.",
 'thm:perkno': "`limitingBelief P (\u03c6 n)` is \u2119\u221e(\u03c6\u2099); `p` with `PolyRatCodes` is the e.c. probability sequence; the two implications match the paper's two displayed clauses (the `_lower`/`_upper` variants split them).",
 'thm:affcoh': "`BoundedAffinePrices`+`hmag` render the paper's bounded \u2130\u2131-progression; `completedAffineLow/High` are the inf/sup of the combination's value over completed worlds; the four chained inequalities are the paper's display.",
 'thm:affpolymax': "Same conclusion shape as the paper, but stated over the bare `BoundedCombinationSequence` \u2014 the price and magnitude bounds are derived from it rather than assumed.",
 'thm:peraffkno': "Future extrema (`affineFutureLow/High`) against the limiting value, the affine analogue of `thm:perkno`; premises are the BCS data only.",
 'thm:affprovind': "The paper's single \u2248-statement appears as its \u2265/\u2264/= comparison forms (`_ge`,`_le`,`_eq`); the world bound quantifies over completed worlds, matching \u2018value \u2265 b in every consistent world\u2019.",
 'thm:nd': "`h\u03c6` says every stage stays jointly consistent *with \u03c6* \u2014 the paper's \u2018\u03c6 consistent with \u0393\u2019 made stagewise. The conclusion (an eventual uniform \u03b5 \u2264 \u2119\u2099(\u03c6)) gives the paper's \u2119\u221e(\u03c6) > 0.",
 'thm:obu': "The c.e. premise is `CEEnumeration`: a program whose dovetailed run returns \u231csource i\u231d at every index \u2014 no clock. The padded repetition the paper builds inside its proof is `EfficientRepeatedEnumeration.ofCE`, padding with `source 0` (the `sound` field forbids \u22a4-padding); `hjoint` is \u0393 \u222a \u03c6\u203e consistent, stagewise.",
 'thm:ob': "\u03ba is genuine prefix complexity: `PrefixMachinePresentation` carries the machine, Kraft bound and coverage; the `UPrefix` endpoints discharge all of it at the constructed universal machine (invariance = `kappaU_le_of_prefixMachine`), leaving the inductor and joint consistency.",
 'thm:dus': "`B.prefixSentence \u03c3` is the paper's conjunction of fresh-symbol literals for the bit string \u03c3; M ranges over lower-semicomputable continuous semimeasures. The caller inputs shown are discharged by constructed witnesses (see the audit note for the \u0398 = \u2205 caveat on the input-free forms).",
 'thm:strict': "The separator presentation (recursively inseparable pair, null stage classes) is constructed; the only input left is computability of the atom G\u00f6del codes. Conclusion: no constant C makes the domination reversible.",
 'thm:scon': "Fixed form adjoins one \u03c8, growing form a whole computable process; the conclusion is the criterion for the *conditioned* history over the union process \u2014 the paper's \u2119\u203e|\u03c8. No joint-consistency premise: the degenerate branch covers unsatisfiable stages.",
 'thm:ifp': "Read the `EfficientPrefixPatch` fields as the real statement: an exactly-quoted prefix patch whose translation preserves the e.c. class. The repo discloses that this interface has no inhabitant \u2014 the one theorem on this page not yet shown to be about anything.",
 'thm:lex': "The premise `payout`-sums to 1 over completed worlds = \u2018exactly one \u03c6\u02b2\u2099 true in each world\u2019; the conclusion sums the k prices to 1 asymptotically.",
 'thm:benford': "Fixed target probability p; `TheoryTruth` says \u0393 decides each \u03c6\u2099 (with truth value truth\u2099); `PseudorandomFrequency` packages the paper's divergent-subsequence frequency condition against a deferral function.",
 'thm:prand': "The varied form: the target sequence p\u2099 enters as a generated feature (`GeneratedRatFeature`), the paper's \u2119\u203e-generability \u2014 so the trader can express the target without computing it.",
 'thm:prandaff': "Affine version over a BCS; `DeterminedViaTheory` is def:affthmval (the combination takes value truth\u2099 in every completed world). Maturity/settlement clocks are constructed inside \u2014 no verifier premises remain.",
 'thm:recunbiasedaff': "Weighted-bias limit point at 0 for a BCS under a generable divergent weighting; premises are the paper's own (determination + weighting), clock-free.",
 'thm:recurringunbiasedness': "Sentence special case of the affine form: `sentenceAffine \u03c6` lifts \u03c6\u2099 to singleton combinations, `TheoryTruth` supplies the determined values.",
 'thm:simcal': "The calibration indicator (price in [a,b]) is itself the weighting; its generability and divergence are the paper's premises; conclusion pins limit points of the weighted truth-average to [a,b].",
 'thm:wub': "The three operational premises are tex's own: generable divergent weighting supported on the deferral image (`hsupport`), strictly increasing f, and `FeedbackTruthComputation` \u2014 the delayed-truth program clocked polynomially at f(k+1), a *weaker* demand than the paper's O(f(n+1)).",
 'thm:wubaff': "Affine version of `thm:wub`; the emitter turning the feedback schedule into an e.c. trade stream is constructed (`FeedbackEmission`), so only the paper's data remains.",
 'thm:recurringunbiasednessexp': "LUV-combination version: `WorldValued` is def:luv's world-value clause, `DeterminedViaTheory` def:affthmval \u2014 both the paper's own representation premises.",
 'thm:prandexp': "Expectation pseudorandomness; same premise pair as above plus the paper's pseudorandomness condition over a deferral function. The `_below`/`_eq` variants are the paper's other comparison directions.",
 'thm:ec': "`hval` is the lem:conluvapprox linkage at the paper's own quantifier (completed worlds); `expectSeq` is \u1d3c\u2099 via the def:e threshold mesh. The conclusion is bare convergence \u2014 the limit is constructed, not hypothesized.",
 'thm:ei': "`IsIndicator` is the paper's 1(\u03c6\u2099) read relationally at completed worlds: Y\u2099 values the truth value of \u03c6\u2099 in every such world. Inhabited by a non-degenerate witness (`indicatorWitness_isIndicator`).",
 'thm:loe': "The paper's \u0393 \u22a2 Z\u2099 = a\u2099X\u2099 + b\u2099Y\u2099 is encoded as: the combination a\u2099X\u2099+b\u2099Y\u2099\u2212Z\u2099 is determined with value 0 (`hdet0`). The conclusion is the paper's asymptotic linearity, unfolded.",
 'thm:expprovind': "`hval` is exactly tex's premise: a one-sided bound on the combination's value over completed worlds, each world free to choose its own valuation \u03bd. The paper's \u2273/\u2272/\u2248 statement appears as the `_ge`/`_le`/`_eq` trio.",
 'lem:mesh': "`S : LUVCombinationSyntax` is the paper's e.c. presentation of the combination sequence (constants, coefficients, LUVs, thresholds by name); the conclusion kills the mesh tail error. Inhabited non-degenerately by `ordinaryLUVCombinationSyntax`.",
 'thm:exppolymax': "Same reading as lem:mesh for the premises; conclusion equates diagonal-expectation extrema with future extrema \u2014 the LUV analogue of `thm:affpolymax`.",
 'thm:expcoh': "The four chained inequalities are the paper's display with `completedLow/High` as the completed-world expectation extrema; the single representation premise is `WorldValued` (def:luv).",
 'thm:perexpkno': "Future expectation extrema against the limiting expectation `expectInf`; same premise set as `thm:expcoh`.",
 'thm:wubexp': "The normalization bound b appears *inside* the feedback premise's type (`C` is about the normalized mesh) \u2014 that is the paper's own \u2018thmval of the combination computable by the deadline\u2019 premise, packaged operationally. Determination is at the paper's combination level (`def:affthmval`); the mesh bridge is built from the vanishing mesh residual, so no per-component-LUV determinedness is assumed.",
 'thm:epr': "Closed over the constructed inductor: the quoted-price LUV is built from the market program itself (`theoremPriceQuoteCode`), so both sides of the paper's display are named objects; only \u03c6\u203e and its codes remain.",
 'thm:er': "Same pattern one level up: the quoted LUV is the market's own day-n expectation of X\u2099; premises are the LUV sequence and its threshold codes.",
 'thm:ceu': "The deferred-price quote `\u2119_f(n)(\u03c6\u2099)` is named by quoting the *program* (deferral costs nothing at emission); premises: \u03c6\u203e, codes, and a bare deferral function.",
 'thm:cee': "Deferred expectation version; `source_valued` is the paper's \u2018X\u2099 is an LUV of \u0393\u2019 (every completed world values it), the one semantic premise.",
 'thm:ccee': "Exact zero-slack endpoint over one non-vacuous canonical process fixed from T. A fixed old-language lift and executable finite-entailment gate internally admit every arbitrary e.c. source satisfying the paper's completed-world [0,1]-valued premise; deferred weight, exact product, and right quotation are constructed internally.",
 'thm:ref': "The interval sentence \u231ca\u2099 < \u2119\u2099(\u03c6\u2099) < b\u2099\u231d is constructed from the market's exact rational quote; a,b enter as generated features (the paper's \u2119\u203e-generable bounds), \u03b4 as the e.c. vanishing width; \u03b5\u203e is the paper's \u2018accuracy\u2019 sequence, existentially produced.",
 'thm:lp': "The self-referential \u03c7 \u2248 \u2018\u2119\u2099(\u03c7\u2099) < p\u2019 is the constructed public diagonal (`theoremDiagonalQuoteCode` at parameter p); the conclusion drives its price to p. Width premises are the paper's e.c. vanishing interval.",
 'thm:st': "A is the indicator product 1(\u03c6\u2099)\u00b7Ind, B the confidence indicator Ind(\u2119_f(n)(\u03c6\u2099) > p\u2099) \u2014 both constructed from the market program. The four hypotheses are tex's four: deferral function, e.c. sentences, e.c. positive \u03b4\u203e, generable p\u203e.",
 'thm:halts': "`theoremDP T` is \u0393's provability process (\u0393 = any \u03a3\u2081-sound T \u2287 I\u03a3\u2081, the paper's \u2018represents computations\u2019); machines/inputs with their codes are the e.c. sequences; the sentence is the halting claim, and its price \u2192 1.",
 'thm:loops': "Dual of `thm:halts`: `hloops` is the paper's premise that T *proves* each non-halting; price \u2192 0.",
 'thm:incons': "`SemidecidableComputation` presents the paper's e.c. sequence of inconsistency claims (one machine, varying inputs, truth \u21d4 halting); both conjuncts of the paper's display appear (belief in inconsistency \u2192 1, in consistency \u2192 0).",
 'thm:pac': "`BoundedComputation` carries the claim \u2018consistent up to horizon f(n)\u2019; its `horizon : ComputableHorizon steps` field names the program \u231cf\u231d and asserts no growth bound, so any computable f is admissible \u2014 the paper's own class.",
 'thm:pazfc': "Same shape as `thm:pac` for a stronger theory's consistency claims, same arbitrary-computable-horizon class.",
 'thm:dontwait': "The bounded-halting claim at horizon f(n) never fires (`hnever`), and the belief \u2192 0; `hh : ComputableHorizon horizons` names \u231cf\u231d and leaves the term unevaluated in the claim, so the paper's arbitrary computable horizon is reached.",
}

TIER_LABEL = {'universal':'paper strength · universal',
              'instantiated':'paper strength · instantiated',
              'qualified':'qualified'}

# Finite Factored Sets defines its notation as macros with *optional* first arguments
# (`\newcommand{\ortho}[3][F]`), which the plain `macros` substitution cannot express, so
# the whole layer lives in `pre_macros` with an explicit alternative per macro: the
# bracketed form first, then the defaulted form.  Longest names are listed before their
# prefixes so that `\coc` and `\cod` are not eaten by `\co`.
FFS_PRE_LATEX = [
 (r'\\coc\[([^\]]*)\]\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\2 \\mathbin{\\perp^{\1}_{\5}} \3 \\mid \4'),
 (r'\\coc\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\1 \\mathbin{\\perp^{F}_{\4}} \2 \\mid \3'),
 (r'\\ncod\[([^\]]*)\]\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\2 \\mathbin{\\rightleftharpoons_{\1}} \3 \\mid \4'),
 (r'\\ncod\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\1 \\mathbin{\\rightleftharpoons_{D}} \2 \\mid \3'),
 (r'\\cod\[([^\]]*)\]\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\2 \\mathbin{\\perp_{\1}} \3 \\mid \4'),
 (r'\\cod\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\1 \\mathbin{\\perp_{D}} \2 \\mid \3'),
 (r'\\co\[([^\]]*)\]\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\2 \\mathbin{\\perp^{\1}} \3 \\mid \4'),
 (r'\\co\{([^{}]*)\}\{([^{}]*)\}\{([^{}]*)\}',
  r'\1 \\mathbin{\\perp^{F}} \2 \\mid \3'),
 (r'\\ortho\[([^\]]*)\]\{([^{}]*)\}\{([^{}]*)\}', r'\2 \\mathbin{\\perp^{\1}} \3'),
 (r'\\ortho\{([^{}]*)\}\{([^{}]*)\}', r'\1 \\mathbin{\\perp^{F}} \2'),
 (r'\\parts\[([^\]]*)\]', r'\\text{Part}(\1)'),
 (r'\\parts(?![A-Za-z])', r'\\text{Part}(S)'),
 (r'\\du\{([^{}]*)\}', r'\\bigsqcup(\1)'),
 (r'\\pr\{([^{}]*)\}', r'\\bigsqcap(\1)'),
]


# Factored Space Models keeps its notation in `meta/environment.tex` as ~100 ordinary
# `\newcommand`s (fixed arity, no optional arguments), so the layer is *derived* from
# that file rather than transcribed: each `\newcommand{\name}[n]{body}` becomes one
# `pre_macros` entry (they are applied repeatedly, so bodies may use other macros).  A
# few bodies are typographic (`\text{\Large$\times$}`, `\ding`) and are overridden with a
# MathML-renderable equivalent below.
FSM_MACRO_OVERRIDES = {
    'timesbig': r'\bigtimes',
    'indep': r'\perp\!\!\!\perp',
    'Obs': r'\text{Obs}',
    'Val': r'\text{Val}',
    'orthF': r'\perp^{\Omega}',
    'orthnotF': r'\not\perp^{\Omega}',
    'orthnot': r'\not\perp',
    'beforeF': r'\leq^{\Omega}',
    'strictlybeforeF': r'<^{\Omega}',
    'FSMG': r'\mathcal{M}^G',
    'timesOmg': r'\bigtimes_{i\in I}\Omega_i',
    'historyC': r'\operatorname{Cohistory}',
    'history': r'\mathcal{H}',
    'thick': r'\;',
    'cmark': r'\checkmark', 'xmark': r'\times',
}


def macros_from_environment(path, overrides):
    """`pre_macros` entries derived from a paper's `\newcommand`s (see FSM_MACRO_OVERRIDES)."""
    text = read(path)
    text = '\n'.join(paper_nodes.strip_tex_comment(l) for l in text.splitlines())
    out = []
    pat = re.compile(r'\\(?:newcommand|renewcommand|DeclareMathOperator)\*?\{?\\([A-Za-z@]+)\}?'
                     r'(?:\[([0-9])\])?\{')
    for m in pat.finditer(text):
        name, arity = m.group(1), int(m.group(2) or 0)
        if '@' in name:
            continue
        # balanced-brace body
        depth, k = 1, m.end()
        while k < len(text) and depth:
            depth += {'{': 1, '}': -1}.get(text[k], 0)
            k += 1
        body = text[m.end():k - 1]
        if text[m.start():m.end()].startswith('\\DeclareMathOperator'):
            body = r'\operatorname{' + body + '}'
        body = overrides.get(name, body)
        if name in ('paragraph', 'schapter', 'epsilon'):
            continue
        rep = body.replace('\\', '\\\\')
        for k_ in range(1, arity + 1):
            rep = rep.replace('#%d' % k_, '\\%d' % k_)
        args = ''.join(r'\{([^{}]*)\}' for _ in range(arity))
        out.append((r'\\' + name + (args if arity else r'(?![A-Za-z])'), rep))
    # `\optionalbracket{\name}{body}` (this paper's `environment.tex`): `\name{arg}` prints
    # as `body(arg)` and a bare `\name` as `body`.
    for m in re.finditer(r'\\optionalbracket\{\\([A-Za-z]+)\}\{', text):
        name = m.group(1)
        depth, k = 1, m.end()
        while k < len(text) and depth:
            depth += {'{': 1, '}': -1}.get(text[k], 0)
            k += 1
        body = overrides.get(name, text[m.end():k - 1]).replace('\\', '\\\\')
        out.append((r'\\' + name + r'\{([^{}]*)\}', body + r'(\1)'))
        out.append((r'\\' + name + r'(?![A-Za-z])', body))
    # longest names first, so `\orthF` is not eaten by `\orth`
    out.sort(key=lambda pr: -len(pr[0]))
    return out


PAPERS_EDITORIAL = {
    'logical-induction': {
        'macros': LI_MACRO_LATEX, 'pre_macros': LI_PRE_LATEX,
        'sections': r'\\(section|subsection)\{([^\n]*)', 'appendix': False,
    },
    'cartesian-frames': {
        'macros': CF_MACRO_LATEX, 'pre_macros': (),
        'sections': r'\\(section|subsection|subsubsection)\{([^\n]*)', 'appendix': True,
    },
    'modal-agents': {
        'macros': MA_MACRO_LATEX, 'pre_macros': (),
        'sections': r'\\(section)\*?\{([^\n]*)', 'appendix': False,
    },
    'finite-factored-sets': {
        'macros': (), 'pre_macros': FFS_PRE_LATEX,
        'sections': r'\\(section|subsection)\{([^\n]*)', 'appendix': False,
    },
    'factored-space-models': {
        'macros': (),
        'pre_macros': macros_from_environment('FactoredSpaces/notes/meta/environment.tex',
                                              FSM_MACRO_OVERRIDES),
        'sections': r'\\(section|subsection)\*?\{([^\n]*)', 'appendix': True,
    },
    # No TeX, hence no macro layer and no `\section` pattern: sectioning is read off the
    # extraction's own page layout, and statements are shown verbatim.
    'condensation': {
        'macros': (), 'pre_macros': (),
        'sections': paper_nodes.printed_extraction_sections, 'appendix': False,
        'renderer': ExtractionRenderer,
        # Statement-first at milestone M1 (historical; at M2 all proofs landed): the statements are final, a good many of the
        # proofs are not.  No count here on purpose — the generator reads both blocks of
        # `AxiomAudit.lean` at run time, so a number written into this comment buys
        # nothing and goes stale the moment a proof lands.  Naming the two blocks here is
        # the whole opt-in — see `staging_for` — and it is what stops a `sorry` from
        # rendering indistinguishably from a proof.
        'inventory_block': 'CONDENSATION-INVENTORY',
        'pending_block': 'CONDENSATION-PENDING',
    },
}


def source_tag(paper):
    """The exact version committed, named the way the paper is citable.

    `arXiv:1609.03543v5` for a preprint; for a paper with no preprint record the
    OpenReview id, and failing that the committed source's own filename — never a
    fabricated arXiv id.
    """
    if paper.get('arxiv'):
        stem = os.path.basename(paper['source']).removesuffix('-main.tex')
        return 'arXiv:' + stem
    if paper.get('openreview'):
        return 'OpenReview:' + paper['openreview']
    return os.path.basename(paper['source'])


def anchor_for(prefix, node_id):
    return prefix + re.sub(r'[^A-Za-z0-9]+', '-', node_id).strip('-').lower()


# ======================================================================
# Logical Induction section — tiered, with reading and audit notes
# ======================================================================

def build_logical_induction(paper, warnings):
    tex = read(paper['source'])
    renderer = TexRenderer(LI_MACRO_LATEX, LI_PRE_LATEX)

    rows = {}
    for line in open(ROOT + paper['coverage_table'], encoding='utf-8'):
        m = re.match(r'\| (\S+) \| (\w+) \| (.*) \|\s*$', line)
        if m and m.group(1) != 'label':
            rows[m.group(1)] = {'tier': m.group(2), 'just': m.group(3).strip()}

    library = LeanLibrary(paper['library'])
    names = audit_inventory_names(read('AxiomAudit.lean'))
    for extra in LI_MANUAL.values():
        for n in extra:
            if n not in names: names.append(n)

    label_eps, eps_all = {}, {}
    for n in names:
        e = library.extract(n)
        if e is None:
            continue  # names of other libraries, or AxiomAudit-local — out of scope here
        eps_all[n] = e
        for lab in e['labels']:
            label_eps.setdefault(lab, []).append(n)

    conf = PAPERS_EDITORIAL['logical-induction']
    located = paper_nodes.latex_label_declarations(tex, list(rows))
    sections = section_titles(tex, conf['sections'], conf['appendix'])

    info = {}
    for lab, row in rows.items():
        node = located.get(lab)
        if node is None:
            warnings.append('logical-induction: %s has no \\label in the paper source' % lab)
            continue
        eps = LI_MANUAL.get(lab, []) + [e for e in label_eps.get(lab, [])
                                        if e not in LI_MANUAL.get(lab, [])]
        eps = [e for e in eps if e in eps_all]
        if not eps:
            warnings.append('logical-induction: %s has no inventory endpoint' % lab)
            continue
        info[lab] = (node, row, eps)

    missing = [lab for lab in rows if lab not in info]
    assert not missing, 'labels with no endpoint: %s' % missing

    counts = {'universal': 0, 'instantiated': 0, 'qualified': 0}
    nav, cards = [], []
    tag = source_tag(paper)
    for sec, group in group_by_section([n for n, _, _ in info.values()], sections):
        nav.append('<div class="nav-sec">%s</div>' % html.escape(sec))
        cards.append('<h2 class="sec" id="sec-%s">%s</h2>'
                     % (re.sub(r'\W+', '-', sec), html.escape(sec)))
        for node in group:
            lab = node.id
            _, row, eps = info[lab]
            counts[row['tier']] += 1
            prim = [p for p in LI_PRIMARY.get(lab, []) if p in eps_all] or eps[:1]
            ordered = prim + [e for e in eps if e not in prim]
            anchor = lab.replace(':', '-')
            nav.append('<a class="nav-item" href="#%s" data-node="%s"><span class="dot %s"></span>%s</a>'
                       % (anchor, anchor, row['tier'], lab))
            notes = []
            if lab in LI_READING:
                notes.append(note('reading-note', 'How the panes line up', md_inline(LI_READING[lab])))
            notes.append(audit_footer('What to check', md_inline(row['just'])))
            cards.append(render_card(
                anchor=anchor, lab=lab, title=node.title,
                badge='<span class="tier %s">%s</span>' % (row['tier'], TIER_LABEL[row['tier']]),
                source=tag, paper_html=renderer.block(node.body, lab),
                endpoints=[(p, eps_all[p]) for p in ordered], notes=notes))

    warnings += renderer_warnings('logical-induction', renderer)
    return {'nav': nav, 'cards': cards, 'counts': counts, 'total': len(info)}


# ======================================================================
# Correspondence sections — Cartesian Frames and ModalAgents
# ======================================================================

def annotated_endpoints(paper, node_id_re):
    """node id -> [(qualified name, extracted statement)], in source order."""
    lib = paper['library']
    library = LeanLibrary(lib)
    anns = paper_nodes.collect_annotations(ROOT + lib + '.lean', ROOT + lib, node_id_re)
    by_node = {}
    carriers = set()
    for a in sorted(anns, key=lambda a: (str(a.path), a.decl_line)):
        f = str(a.path)
        # `decl_line` is 1-based and may land on an attribute line.
        idx = a.decl_line - 1
        ls = library.files[f]
        while idx < len(ls) and (ls[idx].strip().startswith('@[') or not ls[idx].strip()):
            idx += 1
        e = library.extract_at(f, idx)
        carriers.add(a.qualified)
        for node_id in a.nodes:
            by_node.setdefault(node_id, []).append((a.qualified, e))
    return by_node, carriers


def cartesian_frames_errata(paper):
    """Erratum headline per node, from the committed errata file."""
    if not paper.get('errata'):
        return {}
    text = read(paper['errata'])
    out = {}
    for m in re.finditer(r'^\s*(\d+)\.\s+\*\*(.+?)\*\*', text, re.M):
        number, headline = m.group(1), m.group(2)
        ids = re.findall(r'(Definition|Claim|Theorem)s?\s+([0-9]+)(?:\s+and\s+([0-9]+))?',
                         headline)
        for kind, first, second in ids:
            for n in (first, second):
                if n:
                    out.setdefault('%s %s' % (kind, n), []).append((number, headline))
    return out


def cartesian_frames_deviation(paper):
    """The user-ruled intentional deviations, keyed by the node each one governs."""
    if not paper.get('knowledge'):
        return {}
    text = read(paper['knowledge'])
    m = re.search(r'^## Intentional deviations.*?$(.*?)^## ', text, re.S | re.M)
    if not m:
        return {}
    out = {}
    for block in re.split(r'\n(?=\*\*)', m.group(1).strip()):
        head = re.match(r'\*\*(.+?)\*\*', block, re.S)
        if not head:
            continue
        ids = re.findall(r'(Definition|Claim|Theorem)\s+([0-9]+)', head.group(1))
        body = re.sub(r'\s+', ' ', block).strip()
        for kind, number in ids:
            out['%s %s' % (kind, number)] = body
    return out


def build_correspondence(key, paper, warnings, *, extras=None):
    """A paper node beside its Lean endpoints, with no invented tier or audit note."""
    conf = PAPERS_EDITORIAL[key]
    tex = read(paper['source'])
    renderer = (conf['renderer']() if conf.get('renderer')
                else TexRenderer(conf['macros'], conf['pre_macros']))
    # Not `SCHEMES[paper['scheme']]`: the parser depends on the *source format* too, and
    # reading an extraction with the TeX parser fails silently rather than loudly.
    scheme = paper_nodes.scheme_of(paper)

    located = scheme['declarations'](tex)
    numbered = scheme['source_nodes'](tex)
    by_node, carriers = annotated_endpoints(paper, scheme['node_id_re'])

    renderable, unrenderable = [], []
    for node_id in by_node:
        if node_id in located:
            renderable.append(node_id)
        else:
            unrenderable.append(node_id)
    for node_id in sorted(unrenderable):
        warnings.append(
            '%s: %s is cited in Lean and numbered in the source, but its printed '
            'statement could not be located — omitted from the page' % (key, node_id))

    staging = staging_for(key, paper, warnings)
    extras = extras or {}
    prefix = {'cartesian-frames': 'cf-', 'modal-agents': 'ma-',
              'finite-factored-sets': 'ffs-', 'condensation': 'cd-',
              'factored-space-models': 'fsm-'}[key]
    # `condensation` supplies a callable (its sectioning is read off the text
    # extraction's page layout); every TeX-backed paper supplies a `\section` regex.
    sections = (conf['sections'](tex) if callable(conf['sections'])
                else section_titles(tex, conf['sections'], conf['appendix']))
    tag = source_tag(paper)
    nav, cards = [], []
    for sec, group in group_by_section([located[n] for n in renderable], sections):
        nav.append('<div class="nav-sec">%s</div>' % html.escape(sec))
        cards.append('<h2 class="sec" id="sec-%s-%s">%s</h2>'
                     % (prefix.rstrip('-'), re.sub(r'\W+', '-', sec), html.escape(sec)))
        for node in group:
            anchor = anchor_for(prefix, node.id)
            names = [n for n, _ in by_node[node.id]]
            dot = 'plain' if staging is None else staging.dot(names)
            nav.append('<a class="nav-item" href="#%s" data-node="%s"><span class="dot %s"></span>%s</a>'
                       % (anchor, anchor, dot, html.escape(node.id)))
            notes = [n for n in (f(node) for f in extras.values()) if n]
            badge = '<span class="kind">%s</span>' % html.escape(node.kind.lower())
            if staging is not None:
                badge += staging.node_badge(names)
                notes += staging.note(names)
            cards.append(render_card(
                anchor=anchor, lab=node.id, title=node.title, badge=badge,
                source=tag, paper_html=renderer.block(node.body, node.id),
                endpoints=by_node[node.id], notes=notes, staging=staging))

    rendered = sorted({n for node_id in renderable for n, _ in by_node[node_id]})
    if staging is not None:
        for name in rendered:
            if staging.state(name) is None:
                warnings.append(
                    '%s: %s carries an annotation but is in neither the %s nor the %s '
                    'block of AxiomAudit.lean, so the page cannot say whether it is '
                    'proved — rendered unbadged' % (key, name, staging.inventory_block,
                                                    staging.pending_block))
        cards.insert(0, staging.legend(rendered))

    warnings += renderer_warnings(key, renderer)
    return {'nav': nav, 'cards': cards, 'total': len(renderable),
            'numbered': numbered, 'covered': set(renderable), 'carriers': carriers,
            'staging': staging, 'rendered': rendered}


# ======================================================================
# Page assembly
# ======================================================================

def main():
    warnings = []

    li = build_logical_induction(PAPERS['logical-induction'], warnings)

    cf_paper = PAPERS['cartesian-frames']
    errata = cartesian_frames_errata(cf_paper)
    deviation = cartesian_frames_deviation(cf_paper)

    def cf_erratum_note(node):
        entries = errata.get(node.id)
        if not entries:
            return ''
        body = '; '.join('<strong>#%s</strong> %s' % (n, md_inline(h)) for n, h in entries)
        return audit_footer('Paper erratum', body +
                            ' <span class="cite">(%s)</span>' % html.escape(cf_paper['errata']))

    def cf_deviation_note(node):
        body = deviation.get(node.id)
        if not body:
            return ''
        return note('deviation-note', 'Intentional deviation (user ruling)', md_inline(body))

    cf = build_correspondence('cartesian-frames', cf_paper, warnings,
                              extras={'deviation': cf_deviation_note,
                                      'erratum': cf_erratum_note})

    ma_paper = PAPERS['modal-agents']
    ma = build_correspondence('modal-agents', ma_paper, warnings)

    ffs_paper = PAPERS['finite-factored-sets']
    ffs = build_correspondence('finite-factored-sets', ffs_paper, warnings)

    fsm_paper = PAPERS['factored-space-models']
    fsm = build_correspondence('factored-space-models', fsm_paper, warnings)

    cd_paper = PAPERS['condensation']
    cd = build_correspondence('condensation', cd_paper, warnings)
    cd_uncited = sorted(set(cd['numbered']) - cd['covered'],
                        key=paper_nodes.printed_extraction_node_sort_key)
    cd_missing_html = (
        ', '.join('<code>%s</code>' % html.escape(n) for n in cd_uncited)
        if cd_uncited else 'none — every numbered node carries a Lean statement')

    # --- ModalAgents: inventoried endpoints that deliberately carry no annotation ---
    ma_inventory = inventory_names('MA-INVENTORY', warnings)
    ma_bare = sorted(ma_inventory - ma['carriers'])
    ma_reasons = {}
    readme = read(ma_paper['readme'])
    marker = readme.find('deliberately carry **no** annotation')
    if marker >= 0:
        started = False
        for line in readme[marker:].splitlines():
            stripped = line.strip()
            if not stripped.startswith('|'):
                if started and stripped:
                    break        # the table has ended; stop before unrelated prose
                continue
            started = True
            cells = [c.strip() for c in stripped.strip('|').split('|')]
            if len(cells) != 2 or not cells[0].startswith('`'):
                continue
            for name in re.findall(r'`([^`]+)`', cells[0]):
                ma_reasons[name] = cells[1]
    rows = []
    for name in ma_bare:
        reason = ma_reasons.get(name)
        if reason is None:
            warnings.append('modal-agents: inventoried endpoint %s carries no annotation '
                            'and no recorded reason in %s' % (name, ma_paper['readme']))
        rows.append('<tr><td><code>%s</code></td><td>%s</td></tr>'
                    % (html.escape(name),
                       md_inline(reason) if reason
                       else '<em class="unrecorded">no reason recorded</em>'))
    ma_bare_rows = ''.join(rows)

    ma_missing = sorted(ma['numbered'] - ma['covered'],
                        key=lambda s: [int(p) for p in s.split()[1].split('.')])
    ma_missing_html = ', '.join('<code>%s</code>' % html.escape(n) for n in ma_missing)

    ffs_missing = sorted(ffs['numbered'] - ffs['covered'],
                         key=lambda t: (t.split()[0], int(t.split()[1])))
    ffs_by_kind = {}
    for node in ffs_missing:
        ffs_by_kind.setdefault(node.split()[0], []).append(node.split()[1])
    ffs_missing_html = (
        '; '.join('%d of the paper\u2019s %ss' % (len(v), k.lower())
                  for k, v in sorted(ffs_by_kind.items()))
        or 'none — every numbered node of the paper has a Lean statement')

    def fsm_key(t):
        sec, n = t.split()[1].split('.')
        return (sec.isdigit(), sec if not sec.isdigit() else int(sec), int(n))
    fsm_missing = sorted(fsm['numbered'] - fsm['covered'], key=fsm_key)
    fsm_missing_html = (', '.join('<code>%s</code>' % html.escape(n) for n in fsm_missing)
                        or 'none — every numbered node of the paper has a Lean statement')

    cf_missing = sorted(cf['numbered'] - cf['covered'],
                        key=lambda s: int(s.split()[1]))
    cf_missing_html = (', '.join('<code>%s</code>' % html.escape(n) for n in cf_missing)
                       or 'none — every numbered node of the paper has a Lean statement')

    # --- the Cartesian Frames inventory preamble, quoted rather than paraphrased ---
    audit_src = read('AxiomAudit.lean')
    m = re.search(r'/-!\s*## Cartesian Frames — endpoint inventory\s*(.*?)-/', audit_src, re.S)
    cf_inventory_note = md_inline(re.sub(r'\s*\n\s*', ' ', m.group(1)).strip()) if m else ''

    # --- Tier-2 frozen structures, split by the library they belong to ---
    t2 = re.findall(r'#assert_fields (\S+)\n((?:  [^\n]*\n)*)', audit_src)
    def t2rows(pred):
        return ''.join('<tr><td><code>%s</code></td><td>%s</td></tr>' % (
            html.escape(n), ' '.join('<code class="fld">%s</code>' % f for f in flds.split()))
            for n, flds in t2 if pred(n))
    t2_li = t2rows(lambda n: not n.startswith('CartesianFrames.'))
    t2_cf = t2rows(lambda n: n.startswith('CartesianFrames.'))

    # --- index table ---
    # The Condensation row's editorial is generated rather than written, so the number
    # of staged endpoints it quotes cannot drift from the pending block it counts.
    if cd['staging'] is None:
        cd_editorial = (
            '<strong>in progress (milestone M2)</strong> — every in-scope node proved; '
            'no staging block')
    else:
        cd_proved, cd_staged = cd['staging'].counts(cd['rendered'])
        cd_editorial = (
            '<strong>in progress (milestone M2; read-through outstanding)</strong> — every '
            'in-scope node has a proved carrier, and each declaration is badged: %d <em>axiom-clean</em>, '
            '%d <em>staged</em> (statement final, proof still <code>sorry</code>). '
            'Nothing badged staged is claimed proved'
            % (cd_proved, cd_staged))
    cd_editorial += ('. The cards show the paper statement beside the Lean statement '
                     'that carries it, so the section grows as the formalization lands; '
                     '<strong>no strength classification exists for this paper</strong>')
    index_rows = ''
    for key, section, editorial in (
            ('logical-induction', li,
             'tier badge per node (universal / instantiated / qualified), a reading note '
             'and a "what to check" note, from the machine-checked strength table'),
            ('cartesian-frames', cf,
             'errata cross-references and the Claim 35 intentional-deviation ruling; '
             '<strong>no strength classification exists for this paper</strong>'),
            ('modal-agents', ma,
             'scope notes and the deliberately-unannotated inventory endpoints; '
             '<strong>no strength classification exists for this paper</strong>'),
            ('finite-factored-sets', ffs,
             '<strong>complete</strong> — §2–§7; 87 nodes carried by declarations and '
             'nine rendered by Mathlib vocabulary, 96 in scope. Conjecture 1 is stated '
             'as a <code>Prop</code> and deliberately not proved, and Examples 3 and 4 '
             'are out of scope by ruling; <strong>no strength classification exists for '
             'this paper</strong>'),
            ('factored-space-models', fsm,
             '<strong>in progress</strong> — the correspondence view of what is landed so '
             'far; <strong>no strength classification exists for this paper</strong>'),
            ('condensation', cd, cd_editorial)):
        p = PAPERS[key]
        if p.get('arxiv'):
            cite_link = ('<a href="https://arxiv.org/abs/%s">arXiv:%s</a>'
                         % (p['arxiv'], p['arxiv']))
        elif p.get('url'):
            cite_link = ('<a href="%s">OpenReview:%s</a>'
                         % (html.escape(p['url'], quote=True),
                            html.escape(p.get('openreview', 'record'))))
        else:
            cite_link = html.escape(os.path.basename(p['source']))
        index_rows += (
            '<tr><td><a href="#paper-%s">%s</a><div class="idx-cite">%s (%d) · '
            '%s</div></td>'
            '<td class="count">%d</td><td><code>%s/</code></td><td>%s</td></tr>'
            % (key, html.escape(p['title']), html.escape(p['authors']), p['year'],
               cite_link, section['total'], html.escape(p['library']), editorial))

    total_nodes = (li['total'] + cf['total'] + ma['total'] + ffs['total']
                   + fsm['total'] + cd['total'])

    page = read('scripts/trust-surface-template.html')
    for placeholder, value in (
            ('%%NAV_LI%%', '\n'.join(li['nav'])),
            ('%%NAV_CF%%', '\n'.join(cf['nav'])),
            ('%%NAV_MA%%', '\n'.join(ma['nav'])),
            ('%%NAV_FFS%%', '\n'.join(ffs['nav'])),
            ('%%NAV_FSM%%', '\n'.join(fsm['nav'])),
            ('%%NAV_CD%%', '\n'.join(cd['nav'])),
            ('%%CARDS_LI%%', '\n'.join(li['cards'])),
            ('%%CARDS_CF%%', '\n'.join(cf['cards'])),
            ('%%CARDS_MA%%', '\n'.join(ma['cards'])),
            ('%%CARDS_FFS%%', '\n'.join(ffs['cards'])),
            ('%%CARDS_FSM%%', '\n'.join(fsm['cards'])),
            ('%%CARDS_CD%%', '\n'.join(cd['cards'])),
            ('%%CD_MISSING%%', cd_missing_html),
            ('%%NCD%%', str(cd['total'])),
            ('%%INDEX%%', index_rows),
            ('%%T2ROWS%%', t2_li),
            ('%%T2ROWS_CF%%', t2_cf),
            ('%%CF_INVENTORY_NOTE%%', cf_inventory_note),
            ('%%CF_MISSING%%', cf_missing_html),
            ('%%MA_BARE_ROWS%%', ma_bare_rows),
            ('%%MA_MISSING%%', ma_missing_html),
            ('%%FFS_MISSING%%', ffs_missing_html),
            ('%%FSM_MISSING%%', fsm_missing_html),
            ('%%NTOTAL%%', str(total_nodes)),
            ('%%NLI%%', str(li['total'])),
            ('%%NCF%%', str(cf['total'])),
            ('%%NMA%%', str(ma['total'])),
            ('%%NFFS%%', str(ffs['total'])),
            ('%%NFSM%%', str(fsm['total'])),
            ('%%NUNI%%', str(li['counts']['universal'])),
            ('%%NINS%%', str(li['counts']['instantiated'])),
            ('%%NQ%%', str(li['counts']['qualified']))):
        assert placeholder in page, 'template is missing %s' % placeholder
        page = page.replace(placeholder, value)
    left = re.findall(r'%%[A-Z_]+%%', page)
    assert not left, 'template placeholders never filled: %s' % sorted(set(left))

    # Machine-readable coverage stamp: `check_paper_wiring.py` requires every registered
    # paper to appear here with a positive node count, so "the guide covers this paper"
    # is checked against what was actually rendered, not against a title string.
    page += ('\n<!-- trust-surface-papers: %s -->\n'
             % ' '.join('%s=%d' % (k, s['total']) for k, s in
                        (('logical-induction', li), ('cartesian-frames', cf),
                         ('modal-agents', ma), ('finite-factored-sets', ffs),
                         ('factored-space-models', fsm),
                         ('condensation', cd))))
    page += ('\n<!-- trust-surface-sources: %s -->\n'
             % paper_nodes.trust_surface_hash(ROOT))
    open(ROOT + 'docs/trust-surface.html', 'w', encoding='utf-8').write(page)

    print('wrote docs/trust-surface.html — %d nodes (%d Logical Induction, '
          '%d Cartesian Frames, %d ModalAgents, %d Finite Factored Sets, '
          '%d Factored Space Models, %d Condensation)'
          % (total_nodes, li['total'], cf['total'], ma['total'], ffs['total'],
             fsm['total'], cd['total']))
    for w in warnings:
        print('  note: %s' % w)


if __name__ == '__main__':
    main()
