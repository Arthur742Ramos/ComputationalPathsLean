\NeedsTeXFormat{LaTeX2e}[2009/09/24]
\ProvidesClass{sajl} [2014/08/12 v1.0 LaTeX document class for South American Journal of Logic]
\LoadClass[11pt]{article}
\usepackage{graphicx,float,multicol}
\newcommand{\volume}[1]{\gdef\@volume{#1}}
\global\let\@volume\@empty
\newcommand{\issue}[1]{\gdef\@issue{#1}}
\global\let\@issue\@empty
\renewcommand{\year}[1]{\gdef\@year{#1}}
\global\let\@year\@empty
\newcommand{\authorname}[1]{\noindent {#1} \newline}
\newcommand{\address}[1]{#1 \newline}
\newcommand{\email}[1]{ \textit{E-mail: }\texttt{#1} \vspace{0.5cm}}
\newcommand{\keywords}[1]{\vspace{0.5cm}\noindent \textbf{Keywords:}\ #1}
\renewcommand*{\title}[2]{\gdef\@shorttitle{#1}\gdef\@title{#2}}
\renewcommand*{\author}[2]{\gdef\@shortauthor{#1}\gdef\@author{#2}}
\renewcommand{\maketitle}{
	\begingroup
    \centering
    \Large\textbf\@title\normalsize\vskip\baselineskip\par
    \@author\vskip\baselineskip\par
  \endgroup
}
\usepackage{calc}
\usepackage[b5paper, twoside, top=2cm, left=2.5cm, right=2cm, bottom=2cm, includehead]{geometry}
\@twosidetrue
\renewcommand{\@oddhead}{\hfill \textsc{\@shorttitle} \hfill \thepage}%
\renewcommand{\@evenhead}{\thepage \hfill \textsc{\@shortauthor} \hfill}%
\renewcommand{\@oddfoot}{}%
\renewcommand{\@evenfoot}{\@oddfoot}%
\RequirePackage{lastpage}
\AddToHook{begindocument/end}{%
	\label{FirstPage}
	{
		\begin{multicols}{2}
		{
			\small
			\thispagestyle{empty}
  		\noindent {\em South American Journal of Logic} \newline
	  	\textsf{Advance Access} \newline
  		\textsf{ISSN: 2446-6719} \newline
  	}
  	\begin{flushright}
	  	\includegraphics[scale=0.083]{logo-sajl1}
	  \end{flushright}
	  \end{multicols}
  	\vspace{1cm}
  }
}
\endinput
