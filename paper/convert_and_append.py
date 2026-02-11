#!/usr/bin/env python3
"""Convert chapter files and append to sajl_main.tex."""

import re
import sys

# Citation key mapping: book keys → SAJL bibliography keys
CITE_MAP = {
    'Newman42': 'newman42',
    'Klop92': 'klop92',
    'Terese03': 'terese03',
    'BeCH14': 'bezem14',
    'RDQO18': 'ramos18',
    'Nipkow91': 'nipkow91',  # we'll add this to bibliography
    'Squier94': 'squier94',
    'Leinster04': 'leinster04',
}

def fix_cites(text):
    """Replace cite keys with SAJL-format keys."""
    for old, new in CITE_MAP.items():
        text = text.replace(r'\cite{' + old + '}', r'\cite{' + new + '}')
    return text

def convert_book_to_article(text):
    """Convert \\chapter → \\section, \\section → \\subsection, \\subsection → \\subsubsection."""
    # Use temporary markers to avoid double conversion
    text = re.sub(r'\\chapter\*?\{', '__SAJL_SEC{', text)
    text = re.sub(r'\\chapter\*?\[', '__SAJL_SEC[', text)
    text = re.sub(r'\\subsection\*?\{', '__SAJL_SUBSUB{', text)
    text = re.sub(r'\\subsection\*?\[', '__SAJL_SUBSUB[', text)
    text = re.sub(r'\\section\*?\{', '__SAJL_SUBSEC{', text)
    text = re.sub(r'\\section\*?\[', '__SAJL_SUBSEC[', text)
    
    # Now replace markers with final commands
    text = text.replace('__SAJL_SEC{', r'\section{')
    text = text.replace('__SAJL_SEC[', r'\section[')
    text = text.replace('__SAJL_SUBSEC{', r'\subsection{')
    text = text.replace('__SAJL_SUBSEC[', r'\subsection[')
    text = text.replace('__SAJL_SUBSUB{', r'\subsubsection{')
    text = text.replace('__SAJL_SUBSUB[', r'\subsubsection[')
    
    # Remove \part commands
    text = re.sub(r'\\part\{[^}]*\}\s*\n?', '', text)
    text = re.sub(r'\\part\[[^\]]*\]\{[^}]*\}\s*\n?', '', text)
    
    return text

def convert_article_chapter(text):
    """For files already at section level, just remove \\part commands."""
    text = re.sub(r'\\part\{[^}]*\}\s*\n?', '', text)
    text = re.sub(r'\\part\[[^\]]*\]\{[^}]*\}\s*\n?', '', text)
    return text

def process_file(filepath, is_book_format):
    """Read a file, convert format, fix cites."""
    with open(filepath, 'r') as f:
        text = f.read()
    
    if is_book_format:
        text = convert_book_to_article(text)
    else:
        text = convert_article_chapter(text)
    
    text = fix_cites(text)
    return text

# Chapter definitions: (filepath, is_book_format)
chapters = [
    ('chapters/ch3_rewrite_system.tex', True),
    ('chapters/ch4_groupoid.tex', True),
    ('chapters/ch5_higher_dimensional.tex', True),
    ('chapters/ch6_fundamental_groups.tex', False),
    ('chapters/ch7_spaces.tex', False),
    ('chapters/ch8_fibrations.tex', False),
    ('chapters/ch9_hurewicz.tex', False),
    ('chapters/ch10_advanced.tex', False),
    ('chapters/ch11_metatheory.tex', True),
    ('chapters/ch12_conclusion.tex', True),
]

appendices = [
    ('chapters/appendix_a_rules.tex', True),
]

output_parts = []

# Convert chapters
for filepath, is_book in chapters:
    fmt = "book→article" if is_book else "article (as-is)"
    output_parts.append(f'\n%%%% Converted from {filepath} ({fmt}) %%%%\n')
    text = process_file(filepath, is_book)
    output_parts.append(text)
    print(f'  Converted: {filepath} ({fmt})', file=sys.stderr)

# Appendix
output_parts.append('\n%%%% Appendix %%%%\n')
for filepath, is_book in appendices:
    text = process_file(filepath, is_book)
    output_parts.append(text)
    print(f'  Converted appendix: {filepath}', file=sys.stderr)

# Bibliography
output_parts.append(r'''
%%%% Bibliography %%%%

\begin{thebibliography}{99}

\bibitem{dqor16}
R.~J.~G.~B. de~Queiroz, A.~G. de~Oliveira, and A.~F. Ramos.
\newblock Propositional equality, identity types, and direct computational paths.
\newblock {\em South American Journal of Logic}, 2(2):245--296, 2016.

\bibitem{ramos18}
A.~F. Ramos, R.~J.~G.~B. de~Queiroz, and A.~G. de~Oliveira.
\newblock On the identity type as the type of computational paths.
\newblock {\em Logic Journal of the IGPL}, 26(4):378--399, 2018.

\bibitem{ramos19}
A.~F. Ramos, R.~J.~G.~B. de~Queiroz, and A.~G. de~Oliveira.
\newblock Explicit computational paths.
\newblock {\em South American Journal of Logic}, 5(2):1--52, 2019.

\bibitem{lumsdaine10}
P.~L. Lumsdaine.
\newblock Weak $\omega$-categories from intensional type theory.
\newblock {\em Logical Methods in Computer Science}, 6(3):1--19, 2010.

\bibitem{vdberg11}
B.~van~den~Berg and R.~Garner.
\newblock Types are weak $\omega$-groupoids.
\newblock {\em Proceedings of the London Mathematical Society}, 102(2):370--394, 2011.

\bibitem{hott13}
The Univalent Foundations Program.
\newblock {\em Homotopy Type Theory: Univalent Foundations of Mathematics}.
\newblock Institute for Advanced Study, 2013.

\bibitem{bezem14}
M.~Bezem, T.~Coquand, and S.~Huber.
\newblock A model of type theory in cubical sets.
\newblock In {\em 19th International Conference on Types for Proofs and Programs (TYPES 2013)}, volume~26, pages 107--128, 2014.

\bibitem{cohen18}
C.~Cohen, T.~Coquand, S.~Huber, and A.~M{\"o}rtberg.
\newblock Cubical type theory: A constructive interpretation of the univalence axiom.
\newblock {\em Journal of Automated Reasoning}, 60(2):159--216, 2018.

\bibitem{eckmann62}
B.~Eckmann and P.~J. Hilton.
\newblock Group-like structures in general categories. {I}. {M}ultiplications and comultiplications.
\newblock {\em Mathematische Annalen}, 145:227--255, 1962.

\bibitem{newman42}
M.~H.~A. Newman.
\newblock On theories with a combinatorial definition of ``equivalence''.
\newblock {\em Annals of Mathematics}, 43(2):223--243, 1942.

\bibitem{hatcher02}
A.~Hatcher.
\newblock {\em Algebraic Topology}.
\newblock Cambridge University Press, 2002.

\bibitem{may99}
J.~P. May.
\newblock {\em A Concise Course in Algebraic Topology}.
\newblock University of Chicago Press, 1999.

\bibitem{leinster04}
T.~Leinster.
\newblock {\em Higher Operads, Higher Categories}.
\newblock Cambridge University Press, 2004.

\bibitem{baez95}
J.~C. Baez and J.~Dolan.
\newblock Higher-dimensional algebra and topological quantum field theory.
\newblock {\em Journal of Mathematical Physics}, 36(11):6073--6105, 1995.

\bibitem{klop92}
J.~W. Klop.
\newblock Term rewriting systems.
\newblock In S.~Abramsky, D.~Gabbay, and T.~Maibaum, editors, {\em Handbook of Logic in Computer Science}, volume~2, pages 1--116. Oxford University Press, 1992.

\bibitem{terese03}
Terese.
\newblock {\em Term Rewriting Systems}.
\newblock Cambridge University Press, 2003.

\bibitem{mltt84}
P.~Martin-L{\"o}f.
\newblock {\em Intuitionistic Type Theory}.
\newblock Bibliopolis, Naples, 1984.

\bibitem{burroni93}
A.~Burroni.
\newblock Higher-dimensional word problems with applications to equational logic.
\newblock {\em Theoretical Computer Science}, 115(1):43--62, 1993.

\bibitem{metayer03}
F.~M{\'e}tayer.
\newblock Resolutions by polygraphs.
\newblock {\em Theory and Applications of Categories}, 11(7):148--184, 2003.

\bibitem{lafont09}
Y.~Lafont and F.~M{\'e}tayer.
\newblock Polygraphic resolutions and homology of monoids.
\newblock {\em Journal of Pure and Applied Algebra}, 213(6):966--982, 2009.

\bibitem{squier94}
C.~Squier, F.~Otto, and Y.~Kobayashi.
\newblock A finiteness condition for rewriting systems.
\newblock {\em Theoretical Computer Science}, 131(2):271--294, 1994.

\bibitem{nipkow91}
T.~Nipkow.
\newblock Higher-order critical pairs.
\newblock In {\em Proceedings of the 6th Annual IEEE Symposium on Logic in Computer Science (LICS)}, pages 342--349, 1991.

\bibitem{ravenel86}
D.~C. Ravenel.
\newblock {\em Complex Cobordism and Stable Homotopy Groups of Spheres}.
\newblock Academic Press, 1986.

\bibitem{adams74}
J.~F. Adams.
\newblock {\em Stable Homotopy and Generalised Homology}.
\newblock University of Chicago Press, 1974.

\bibitem{switzer75}
R.~M. Switzer.
\newblock {\em Algebraic Topology: Homotopy and Homology}.
\newblock Springer-Verlag, 1975.

\bibitem{whitehead78}
G.~W. Whitehead.
\newblock {\em Elements of Homotopy Theory}.
\newblock Springer-Verlag, 1978.

\end{thebibliography}
''')

# Author info and end document
output_parts.append(r'''
\medskip

\authorname{Arthur Ferreira Ramos}
\address{Centro de Inform\'atica\\
Federal University of Pernambuco (UFPE)\\
Av. Jornalista An\'ibal Fernandes, s/n, CEP 50740-560, Recife, PE, Brazil}
\email{afr3@cin.ufpe.br}

\authorname{Ruy J.G.B. de Queiroz}
\address{Centro de Inform\'atica\\
Federal University of Pernambuco (UFPE)\\
Av. Jornalista An\'ibal Fernandes, s/n, CEP 50740-560, Recife, PE, Brazil}
\email{ruy@cin.ufpe.br}

\authorname{Anjolina G. de Oliveira}
\address{Centro de Inform\'atica\\
Federal University of Pernambuco (UFPE)\\
Av. Jornalista An\'ibal Fernandes, s/n, CEP 50740-560, Recife, PE, Brazil}
\email{ago@cin.ufpe.br}

\end{document}
''')

# Write everything
result = '\n'.join(output_parts)
print(result)
print(f'\n  Total output characters: {len(result)}', file=sys.stderr)
