#!/usr/bin/env python3
"""Generate docs/trust-surface.html — the trust-surface read-through guide.

Side-by-side of every annotated paper node (notes/1609.03543v5-main.tex) with the
strongest Lean endpoint carrying it, plus the tier and justification from
scripts/coverage-classification.md. Paper math is converted to MathML at build time
(pip install latex2mathml); the page is self-contained, no runtime JS libraries.

Run from the repository root:  python3 scripts/gen-trust-surface.py
Regenerate after any change to the endpoint surface, the coverage table, or the
template (scripts/trust-surface-template.html).
"""

import re, json, glob, os, html

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'

rows = {}
for line in open(ROOT+'scripts/coverage-classification.md'):
    m = re.match(r'\| (\S+) \| (\w+) \| (.*) \|\s*$', line)
    if m and m.group(1) != 'label':
        rows[m.group(1)] = {'tier': m.group(2), 'just': m.group(3).strip()}

tex = open(ROOT+'notes/1609.03543v5-main.tex').read()
def find_env(label):
    pos = tex.find('\\label{%s}' % label)
    if pos < 0: return None, None, None
    start = tex.rfind('\\begin{', 0, pos)
    m = re.match(r'\\begin\{(\w+)\}', tex[start:])
    env = m.group(1)
    end = tex.find('\\end{%s}' % env, pos)
    body = tex[start:end]
    tm = re.match(r'\\begin\{\w+\}(?:\[([^\]]*)\])?(?:\{(\w+)\})?', body)
    title = tm.group(1) or ''
    kind = tm.group(2) or env
    body = re.sub(r'^\\begin\{\w+\}(\[[^\]]*\])?(\{\w+\})?(\{\w+\})?', '', body)
    body = re.sub(r'\\label\{[^}]*\}', '', body)
    return title, kind, body.strip()

# inventory names
src = re.sub(r'/-.*?-/', '', open(ROOT+'AxiomAudit.lean').read(), flags=re.S)
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
names = [n for n in dict.fromkeys(names)]

files = {f: open(f).read().split('\n') for f in glob.glob(ROOT+'LogicalInduction/**/*.lean', recursive=True)}

def find_decl(name):
    short = name.split('.')[-1]
    pat = re.compile(r'^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|structure|class|abbrev)\s+([\w.\x27]+)')
    best = (None, None)
    for f, ls in files.items():
        for idx, l in enumerate(ls):
            m = pat.match(l)
            if not m: continue
            written = m.group(2)
            if written == name or name.endswith('.' + written):
                return f, idx     # exact dotted match wins immediately
            if written == short or written.endswith('.' + short):
                if best[0] is None:
                    best = (f, idx)
    return best

def extract(name):
    f, idx = find_decl(name)
    if f is None: return None
    ls = files[f]
    # docstring: scan back
    doc = ''
    j = idx - 1
    # skip attribute/open/set_option lines
    while j >= 0 and (ls[j].strip().startswith(('attribute','set_option','open','@[')) or ls[j].strip()==''):
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
        labels = re.findall(r'`([\w:]+)`', re.search(r'Paper node:(.*)', doc).group(1)) if 'Paper node:' in doc else []
        return {'name': name, 'file': f.replace(ROOT,''), 'sig': sig, 'labels': labels, 'doc': doc}
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
    labels = re.findall(r'`([\w:]+)`', re.search(r'Paper node:(.*)', doc).group(1)) if 'Paper node:' in doc else []
    return {'name': name, 'file': f.replace(ROOT,''), 'sig': sig, 'labels': labels, 'doc': doc}

MANUAL = {
 'def:affcomsen': ['AffineCombination'],
 'def:bap': ['AffineCombination.BoundedCombinationSequence'],
 'def:blcp': ['LUVCombination.BoundedSequence'],
 'def:dedproc': ['DeductiveProcess', 'DeductiveProcessComputation'],
 'def:deferralfunc': ['DeferralFunction'],
 'def:fuz': ['PGenerableWeighting'],
 'def:lic': ['IsLogicalInductor'],
 'def:trader': ['Trader'],
 'def:tradestrat': ['Strategy'],
 'def:luv': ['LUV'],
 'def:ece': ['GeneratedRatFeature'],
 'def:ec': ['EfficientlyComputable'],
 'def:lia': ['liaStates'],
}
label_eps = {}
eps_all = {}
for extra in MANUAL.values():
    for n in extra:
        if n not in names: names.append(n)
for n in names:
    e = extract(n)
    if e is None:
        continue  # ModalAgents / AxiomAudit-local names — outside this page's scope
    eps_all[n] = e
    for lab in e['labels']:
        label_eps.setdefault(lab, []).append(n)

out = {}
for lab, row in rows.items():
    title, kind, body = find_env(lab)
    eps = MANUAL.get(lab, []) + [e for e in label_eps.get(lab, []) if e not in MANUAL.get(lab, [])]
    eps = [e for e in eps if e in eps_all]
    out[lab] = {'tier': row['tier'], 'just': row['just'], 'title': title,
                'kind': kind, 'paper': body,
                'endpoints': eps}

DATA = {'labels': out, 'eps': eps_all}
missing = [l for l, v in out.items() if not v['endpoints']]
assert not missing, 'labels with no endpoint: %s' % missing


# ======================================================================
# Page generation
# ======================================================================

LB, EPS = DATA['labels'], DATA['eps']
# ---------------- tex -> html ----------------
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

def replace_nested(s, macro, fmt):
    """Replace \\macro{...} with fmt % inner, handling one nesting level robustly."""
    pat = '\\\\' + macro + '{'
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
    s = re.sub(r'\\mathcal\{([^{}]*)\}', r'𝒞\1', s) if False else s
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


import latex2mathml.converter as _l2m

MACRO_LATEX = [
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
PRE_LATEX = [
 (r'\\seq\s*\{', r'\\overline{'),
 (r'\\seq\s*(\\[A-Za-z]+)', r'\\overline{\1}'),
 (r'\\seq\s+([A-Za-z])', r'\\overline{\1}'),
 (r'\\enc\s*\{', r'\\underline{'),
 (r'\\enc\s*(\\[A-Za-z]+)', r'\\underline{\1}'),
 (r'\\gen\s*(\\[A-Za-z]+)', r'{\1}^{\\dagger}'),
 (r'\\gen\{([^{}]*)\}', r'{\1}^{\\dagger}'),
 (r'\\gen\s+([A-Za-z])', r'{\1}^{\\dagger}'),
]
def expand_latex(seg):
    for _ in range(3):
        for pat, rep in PRE_LATEX:
            seg = re.sub(pat, rep, seg)
    for pat, rep in MACRO_LATEX:
        if re.fullmatch(r'[A-Za-z0-9]+', rep):
            rep = '{' + rep + '}'
        seg = re.sub(pat, rep, seg)
    return seg

def quot_close(seg):
    # \quot{X} was opened as \text{\u201c}{X ... need closing \u201d: handle via replace_nested instead
    return seg

def tex2mml(seg, display=False):
    seg = replace_nested(seg, 'quot', '\\text{\u201c}%s\\text{\u201d}')
    seg = replace_nested(seg, 'proofin', '')
    seg = expand_latex(seg)
    try:
        out = _l2m.convert(seg, display='block' if display else 'inline')
        return out
    except Exception:
        h = texmath(seg.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;'))
        cls = 'dm' if display else 'im'
        return '<span class="%s">%s</span>' % (cls, h)

def unescape_html(x):
    return x.replace('&lt;','<').replace('&gt;','>').replace('&amp;','&')

def texblock(s):
    """Full statement body -> html (handles \\[ \\], $..$, itemize, text macros)."""
    s = replace_nested(s, 'proofin', '')
    s = re.sub(r'%[^\n]*', '', s)
    s = re.sub(r'\\(?:noindent|smallskip|medskip|bigskip|par)\b', '', s)
    s = replace_nested(s, 'proofin', '')
    # protect html
    s = s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
    out, i = [], 0
    # split display math
    parts = re.split(r'\\\[|\\\]', s)
    htmlparts = []
    for k, part in enumerate(parts):
        if k % 2 == 1:
            htmlparts.append('<div class="dmath">%s</div>' % tex2mml(unescape_html(part), display=True))
        else:
            # inline math
            txt = part
            segs = re.split(r'\$', txt)
            buf = []
            for j, seg in enumerate(segs):
                if j % 2 == 1:
                    buf.append(tex2mml(unescape_html(seg)))
                else:
                    t = seg
                    t = re.sub(r'\\emph\{([^{}]*)\}', r'<em>\1</em>', t)
                    t = re.sub(r'\\textbf\{([^{}]*)\}', r'<strong>\1</strong>', t)
                    t = re.sub(r'\\textit\{([^{}]*)\}', r'<em>\1</em>', t)
                    t = re.sub(r'\\ref\{[^{}]*\}', '[ref]', t)
                    t = re.sub(r'\\(?:cref|Cref|eqref)\{[^{}]*\}', '[ref]', t)
                    t = t.replace('\\ec[]', 'e.c.').replace('\\ec', 'e.c.')
                    t = t.replace('\\pgenable', 'ℙ‾-generable')
                    t = t.replace('\\begin{itemize}', '<ul>').replace('\\end{itemize}', '</ul>')
                    t = t.replace('\\begin{enumerate}', '<ol>').replace('\\end{enumerate}', '</ol>')
                    t = re.sub(r'\\item\s*', '</li-mark><li>', t)
                    t = t.replace('``', '“').replace("''", '”')
                    t = re.sub(r'\\([A-Za-z]+)', lambda m: SIMPLE.get(m.group(1), GREEK.get(m.group(1), m.group(1))), t)
                    t = t.replace('{','').replace('}','').replace('~',' ')
                    buf.append(t)
            htmlparts.append(''.join(buf))
    res = ''.join(htmlparts)
    # fix list item marks
    res = re.sub(r'&lt;ul&gt;', '<ul>', res)
    res = res.replace('<ul></li-mark>', '<ul>').replace('</li-mark>', '</li>' if False else '')
    res = res.replace('<ul><li>', '<ul><li>')
    # paragraphs
    paras = [p.strip() for p in res.split('\n\n') if p.strip()]
    return '\n'.join('<p>%s</p>' % p if not p.startswith('<div') and not p.startswith('<ul') else p for p in paras)

# section titles by tex position
sec_positions = [(m.start(), m.group(2)) for m in re.finditer(r'\\(section|subsection)\{([^\n]*)', tex)]
def section_of(label):
    pos = tex.find('\\label{%s}' % label)
    best = 'Front matter'
    for p, t in sec_positions:
        if p < pos: best = t
        else: break
    t = best
    t = re.sub(r'\\texorpdfstring\{[^{}]*(?:\{[^{}]*\})?[^{}]*\}\{([^}]*)\}', r'\1', t)
    t = re.sub(r'\\label\{[^}]*\}', '', t)
    t = t.replace('\\LICtitle', 'Logical Induction Criterion').replace('\\LItitle', 'Logical Inductor')
    t = t.replace('\\LIA', 'LIA').replace('\\TradingFirm', 'Trading Firm')
    t = re.sub(r'\\emph\{([^}]*)\}', r'\1', t)
    t = re.sub(r'\$([^$]*)\$', r'\1', t)
    t = re.sub(r'\\[A-Za-z]+ ?', '', t)
    t = t.replace('{','').replace('}','').strip()
    return t or 'Front matter'

# curated primary endpoints (first shown with full signature)
PRIMARY = {
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
 'thm:obu':['lic_uniform_nonDogmatism'],
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
 'thm:ccee':['lic_no_expected_net_update_conditional_closed'],
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
READING = {
 'def:lic': "The class bundles the criterion (`noExploit`, quantified over `EfficientlyComputable` traders) with two facts the paper leaves ambient: the market and the process are computable. `P n \u03c6` is the paper's \u2119\u2099(\u03c6).",
 'def:ec': "The paper's \u201ccomputable in O(poly(n))\u201d becomes: two fixed programs under one polynomial fuel clock emit the day-n strategy's serialized symbol stream. This is the `dd:fuel` substitution itself \u2014 the one place the model is chosen; everything downstream inherits it.",
 'def:dedproc': "`D` and `mono` are the paper's nondecreasing finite sets; the paper's \u201ccomputably enumerable\u201d lives in the separate certificate `DeductiveProcessComputation`, taken as a hypothesis exactly where the paper says \u2018computable deductive process\u2019.",
 'def:trader': "A trader is its day-indexed strategy function; all economic content (holdings, exploitation) is derived, matching the paper's reading of a trader as a strategy sequence.",
 'def:tradestrat': "`trades` is the affine combination (the paper's \u03be\u2081\u03c6\u2081+\u2026); `rank_le` is the paper's rank condition \u2014 an n-strategy mentions only prices of days \u2264 n.",
 'def:affcomsen': "`const` + `terms` = the paper's c + \u03a3 \u03be\u1d62\u03c6\u1d62, with features as `EF` expression trees so that generability is syntactic.",
 'def:bap': "Two fields for the paper's two clauses: `poly` is the e.c. certificate on the combination sequence, `bounded` the single uniform \u2113\u00b9 bound.",
 'def:deferralfunc': "`lt` is f(n) > n; `fueled` renders \u201cf computable in time polynomial in f(n)\u201d as a poly clock in the *output*, exactly as the paper demands (so f may grow fast).",
 'def:ece': "`GeneratedRatFeature` is \u2018\u2119\u203e-generable\u2019: a rank-bounded, polynomially emitted expression whose denotation against the market's own prices is the sequence. Compare clause by clause \u2014 nothing about the values themselves is assumed.",
 'def:fuz': "Same data as `def:ece` minus the denotation clause: the weighting enters as expressions, so a trader can trade on it without knowing its values.",
 'def:luv': "The trust-relevant delta: the paper's LUV is a first-order formula free in one variable; here a LUV *is* its family of threshold atoms `\u231cX > r\u231d` (field `gt`). World-value semantics is supplied per-world by `PCWorld.ValuesAt` \u2014 the disclosed propositional substitution.",
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
 'thm:obu': "The qualified row in one look: `rep : EfficientRepeatedEnumeration source` is the padded repetition the paper *builds inside its proof* from a c.e. source; here it enters as data, and its `sound` field even forbids the paper's \u22a4-padding unless \u22a4 is in the source's range.",
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
 'thm:wubexp': "The normalization bound b appears *inside* the feedback premises' types (`C`/`bridge` are about the normalized mesh) \u2014 that is the paper's own \u2018thmval of the combination computable by the deadline\u2019 premise, packaged operationally. See the audit note for the ExactTheoryPresentation qualification.",
 'thm:epr': "Closed over the constructed inductor: the quoted-price LUV is built from the market program itself (`theoremPriceQuoteCode`), so both sides of the paper's display are named objects; only \u03c6\u203e and its codes remain.",
 'thm:er': "Same pattern one level up: the quoted LUV is the market's own day-n expectation of X\u2099; premises are the LUV sequence and its threshold codes.",
 'thm:ceu': "The deferred-price quote `\u2119_f(n)(\u03c6\u2099)` is named by quoting the *program* (deferral costs nothing at emission); premises: \u03c6\u203e, codes, and a bare deferral function.",
 'thm:cee': "Deferred expectation version; `source_valued` is the paper's \u2018X\u2099 is an LUV of \u0393\u2019 (every completed world values it), the one semantic premise.",
 'thm:ccee': "Left side is the *mesh* product of X\u2099 with the deferred weight (exact to within 1/(n+1) \u2014 the disclosed substitution); right side quotes the market's deferred weighted expectation exactly. The premises are the paper's: arbitrary e.c. source + [0,1] generable weight + deferral function.",
 'thm:ref': "The interval sentence \u231ca\u2099 < \u2119\u2099(\u03c6\u2099) < b\u2099\u231d is constructed from the market's exact rational quote; a,b enter as generated features (the paper's \u2119\u203e-generable bounds), \u03b4 as the e.c. vanishing width; \u03b5\u203e is the paper's \u2018accuracy\u2019 sequence, existentially produced.",
 'thm:lp': "The self-referential \u03c7 \u2248 \u2018\u2119\u2099(\u03c7\u2099) < p\u2019 is the constructed public diagonal (`theoremDiagonalQuoteCode` at parameter p); the conclusion drives its price to p. Width premises are the paper's e.c. vanishing interval.",
 'thm:st': "A is the indicator product 1(\u03c6\u2099)\u00b7Ind, B the confidence indicator Ind(\u2119_f(n)(\u03c6\u2099) > p\u2099) \u2014 both constructed from the market program. The four hypotheses are tex's four: deferral function, e.c. sentences, e.c. positive \u03b4\u203e, generable p\u203e.",
 'thm:halts': "`theoremDP T` is \u0393's provability process (\u0393 = any \u03a3\u2081-sound T \u2287 I\u03a3\u2081, the paper's \u2018represents computations\u2019); machines/inputs with their codes are the e.c. sequences; the sentence is the halting claim, and its price \u2192 1.",
 'thm:loops': "Dual of `thm:halts`: `hloops` is the paper's premise that T *proves* each non-halting; price \u2192 0.",
 'thm:incons': "`SemidecidableComputation` presents the paper's e.c. sequence of inconsistency claims (one machine, varying inputs, truth \u21d4 halting); both conjuncts of the paper's display appear (belief in inconsistency \u2192 1, in consistency \u2192 0).",
 'thm:pac': "`BoundedComputation` carries the claim \u2018consistent up to horizon f(n)\u2019; its `steps_poly` field is the restriction the qualified tier records \u2014 the paper allows any computable f.",
 'thm:pazfc': "Same shape as `thm:pac` for a stronger theory's consistency claims, same `steps_poly` restriction.",
 'thm:dontwait': "The bounded-halting claim at horizon h(n) never fires (`hnever`), and the belief \u2192 0; `hh : PolyNatCodes horizons` restricts the paper's arbitrary computable horizon \u2014 the qualified tier's content.",
}

def md_inline(s):
    s = html.escape(s)
    s = re.sub(r'`([^`]*)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'(?<![*\w])\*([^*\n]+)\*(?![*\w])', r'<em>\1</em>', s)
    return s

# order labels by tex position, group by section
order = sorted(LB.keys(), key=lambda l: tex.find('\\label{%s}' % l))
groups = []
for lab in order:
    sec = section_of(lab)
    if not groups or groups[-1][0] != sec:
        groups.append((sec, []))
    groups[-1][1].append(lab)

TIER_LABEL = {'universal':'paper strength · universal','instantiated':'paper strength · instantiated','qualified':'qualified'}

# Tier-2 structures from AxiomAudit
t2 = re.findall(r'#assert_fields (\S+)\n((?:  [^\n]*\n)*)', open(ROOT+'AxiomAudit.lean').read())
t2rows = ''.join('<tr><td><code>%s</code></td><td>%s</td></tr>' % (
    html.escape(n), ' '.join('<code class="fld">%s</code>' % f for f in flds.split())) for n, flds in t2)

cards = []
nav = []
counts = {'universal':0,'instantiated':0,'qualified':0}
for sec, labs in groups:
    nav.append('<div class="nav-sec">%s</div>' % html.escape(sec))
    cards.append('<h2 class="sec" id="sec-%s">%s</h2>' % (re.sub(r'\W+','-',sec), html.escape(sec)))
    for lab in labs:
        v = LB[lab]
        counts[v['tier']] += 1
        prim = [p for p in PRIMARY.get(lab, []) if p in EPS] or v['endpoints'][:1]
        ordered = prim + [e for e in v['endpoints'] if e not in prim]
        slides = ''
        for i, p in enumerate(ordered):
            e = EPS[p]
            slides += ('<div class="ep-slide%s"><div class="ep-head">'
                       '<code class="ep-name">%s</code><span class="ep-file">%s</span></div>'
                       '<pre class="sig">%s</pre></div>') % (
                '' if i == 0 else ' hidden', html.escape(p), html.escape(e['file']),
                html.escape(e['sig']))
        controls = ''
        if len(ordered) > 1:
            controls = ('<div class="ep-nav"><button class="ep-prev" aria-label="previous endpoint">&#8249;</button>'
                        '<span class="ep-count" data-total="%d">1 / %d</span>'
                        '<button class="ep-next" aria-label="next endpoint">&#8250;</button>'
                        '<span class="ep-nav-hint">inventory endpoints for this node</span></div>') % (
                len(ordered), len(ordered))
        sig_html = controls + slides
        others_html = ''
        anchor = lab.replace(':','-')
        nav.append('<a class="nav-item" href="#%s" data-node="%s"><span class="dot %s"></span>%s</a>' % (anchor, anchor, v['tier'], lab))
        title = v['title'] or ''
        cards.append('''
<article class="node" id="%(anchor)s">
  <header class="node-head">
    <label class="check"><input type="checkbox" data-node="%(anchor)s" aria-label="mark %(lab)s read"></label>
    <span class="node-label">%(lab)s</span>
    <span class="node-title">%(title)s</span>
    <span class="tier %(tier)s">%(tierlabel)s</span>
  </header>
  <div class="panes">
    <section class="paper-pane">
      <div class="pane-tag">Paper · arXiv:1609.03543v5</div>
      %(paper)s
    </section>
    <section class="lean-pane">
      <div class="pane-tag">Lean · statement only (proof body is kernel-checked)</div>
      %(sig)s
      %(others)s
    </section>
  </div>
  %(reading)s
  <footer class="audit-note"><span class="audit-tag">What to check</span> %(just)s</footer>
</article>''' % dict(anchor=anchor, lab=lab, title=html.escape(title), tier=v['tier'],
        tierlabel=TIER_LABEL[v['tier']], paper=texblock(v['paper']), sig=sig_html,
        others=others_html, just=md_inline(v['just']),
        reading=('<div class="reading-note"><span class="reading-tag">How the panes line up</span> %s</div>'
                 % md_inline(READING[lab])) if lab in READING else ''))

body_cards = '\n'.join(cards)
nav_html = '\n'.join(nav)

page = open(ROOT + 'scripts/trust-surface-template.html').read()
page = (page.replace('%%NAV%%', nav_html).replace('%%CARDS%%', body_cards)
            .replace('%%T2ROWS%%', t2rows)
            .replace('%%NUNI%%', str(counts['universal'])).replace('%%NINS%%', str(counts['instantiated']))
            .replace('%%NQ%%', str(counts['qualified'])))
import hashlib
_h = hashlib.sha256()
for _f in ['scripts/coverage-classification.md', 'AxiomAudit.lean',
           'notes/1609.03543v5-main.tex', 'scripts/trust-surface-template.html',
           'scripts/gen-trust-surface.py']:
    _h.update(open(ROOT + _f, 'rb').read())
page += '\n<!-- trust-surface-sources: %s -->\n' % _h.hexdigest()
open(ROOT + 'docs/trust-surface.html', 'w').write(page)
print('wrote docs/trust-surface.html —', sum(len(l) for _, l in groups), 'nodes in', len(groups), 'sections')
