% This is the BSLstyle.cls class file.

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{BSLstyle}[2020/08/01 v1.01 Standard "BSLstyle" LaTeX class]

\LoadClass[twoside]{article}
\RequirePackage{amsmath}
\RequirePackage{amsfonts}
\RequirePackage{amscd}
\RequirePackage{amssymb}
\RequirePackage{mathtools}
\RequirePackage{mathrsfs}
\RequirePackage{graphicx}
\RequirePackage[dvipsnames]{xcolor}
\RequirePackage{tikz}
%\RequirePackage{bussproofs}


% ***************************
% ********** SIZES **********
% ***************************

\renewcommand{\normalsize}{\@setfontsize\normalsize\@xpt{12}
	\abovedisplayskip  8\p@ \@plus2\p@ \@minus4.5\p@
	\abovedisplayshortskip \z@ \@plus2\p@
	\belowdisplayshortskip   8\p@ \@plus2\p@   \@minus4.5\p@
	\belowdisplayskip \abovedisplayskip
	\let\@listi\@listI}
\renewcommand{\small}{%
	\@setfontsize\small\@xpt\@xiipt
	\abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@
	\abovedisplayshortskip \z@ \@plus3\p@
	\belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@
	\def\@listi{\leftmargin\leftmargini
		\topsep 6\p@ \@plus2\p@ \@minus2\p@
		\parsep 3\p@ \@plus2\p@ \@minus\p@
		\itemsep \parsep}%
	\belowdisplayskip \abovedisplayskip
}
\renewcommand{\footnotesize}{\@setsize\footnotesize{9pt}\viiipt\@viiipt
	\abovedisplayskip 6pt minus3pt
	\belowdisplayskip \abovedisplayskip
	\abovedisplayshortskip \z@ plus1pt
	\belowdisplayshortskip 3pt plus1pt minus2pt
	\def\@listi{\leftmargin\leftmargini
		\topsep 4pt plus 2pt minus 2pt
		\parsep 2pt plus 1pt minus 1pt
		\itemsep \parsep}}
\renewcommand{\scriptsize}{\@setsize\scriptsize{9pt}\viiipt\@viiipt}
\renewcommand{\tiny}{\@setsize\tiny{7pt}\vipt\@vipt}
\renewcommand{\large}{\@setsize\large{14pt}\xiipt\@xiipt}   % B
\renewcommand{\Large}{\@setsize\Large{16pt}\xivpt\@xivpt}   % A
\renewcommand{\LARGE}{\@setsize\LARGE{22pt}\xxpt\@xxpt}     % Chap
\renewcommand{\huge}{\@setsize\huge{30pt}\xxvpt\@xxvpt}
\renewcommand{\Huge}{\huge}

 
% *************
% Error message
% *************

\def\@logicerr#1%
{\errhelp{This standard LaTeX command is not used in BSLstyle.cls.
		Try pressing enter, and it'll probably be ignored.}%
	\typeout{Style error. \space See ``Instructions for Authors''}%
	\errmessage{#1}}


% **************************************
% Page dimensions, lineskips, type sizes
% **************************************

\RequirePackage{geometry}

\geometry{asymmetric,%
	top=15pc,%
	left=12pc,%
	height=37\baselineskip,%
	textwidth=27pc,%
	includefoot%
}

\lineskip 1pt 
\normallineskip 1pt
\def\baselinestretch{1}

\normalsize

\footnotesep 8.4pt
\skip\footins 10.8pt plus 4pt minus 2pt
\marginparpush 7pt

\parskip 0pt
\partopsep 1.5pt plus 1pt minus 1pt
\def\chapstrut{\hrule width0pt height24pt depth0pt}
\def\afterchapstrut{\hrule width0pt height12pt depth0pt}


% Penalties
\binoppenalty=2000
\relpenalty=1500
\@lowpenalty 51 \@medpenalty 151 \@highpenalty 301
\@beginparpenalty -\@lowpenalty
\@endparpenalty -\@lowpenalty
\@itempenalty -\@lowpenalty
\clubpenalty 2500
\widowpenalty 2500
\displaywidowpenalty 1500
\predisplaypenalty 500
\postdisplaypenalty 500
\interlinepenalty 0
\brokenpenalty 2000

\@beginparpenalty=\predisplaypenalty
\@endparpenalty=\postdisplaypenalty
\@itempenalty=500


% ******************************
% ********** SECTIONS **********
% ******************************

\RequirePackage{titlesec}

\titleformat{\section}
{\normalfont\large\bfseries\raggedright}{\thesection.}{1em}{}
\titleformat{\subsection}
{\normalfont\normalsize\bfseries\raggedright}{\thesubsection.}{1em}{}
\titleformat{\subsubsection}
{\normalfont\normalsize\bfseries\raggedright}{\thesubsubsection.}{1em}{}
\titleformat{\paragraph}[runin]
{\normalfont\normalsize\bfseries}{\theparagraph}{1em}{}
\titleformat{\subparagraph}[runin]
{\normalfont\normalsize\itshape}{\noindent\thesubparagraph}{1em}{}


% ******************************
% ********** THEOREMS **********
% ******************************

\RequirePackage{amsthm}
\RequirePackage[inline]{enumitem}
\RequirePackage{etoolbox}
\RequirePackage{aliascnt}
\PassOptionsToPackage{hyphens}{url}
\RequirePackage[hidelinks,colorlinks=true,allcolors=blue]{hyperref}
\renewcommand\UrlFont{\normalfont}
\RequirePackage{cleveref}
\RequirePackage{xstring}

\newtheoremstyle{definition} % name
{\topsep}                    % Space above
{\topsep}                    % Space below
{\upshape}                   % Body font
{}                           % Indent amount
{\scshape}                   % Theorem head font
{.}                          % Punctuation after theorem head
{.5em}                       % Space after theorem head
{}

\newtheoremstyle{plain} % name
{\topsep}                    % Space above
{\topsep}                    % Space below
{\itshape}                   % Body font
{}                           % Indent amount
{\scshape}                   % Theorem head font
{.}                          % Punctuation after theorem head
{.5em}                       % Space after theorem head
{}

\newtheoremstyle{remark} % name
{\topsep}                    % Space above
{\topsep}                    		 % Space below
{\upshape}                   % Body font
{}                           % Indent amount
{\itshape}                   % Theorem head font
{.}                          % Punctuation after theorem head
{.5em}                       % Space after theorem head
{}

\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newaliascnt{Lemma}{theorem}
\newtheorem{lemma}[Lemma]{Lemma}
\aliascntresetthe{Lemma}
\crefname{Lemma}{lemma}{lemmas}
\newtheorem*{theorem*}{Theorem}
\newtheorem*{lemma*}{Lemma}

\theoremstyle{definition}
\newaliascnt{Definition}{theorem}
\newtheorem{definition}[Definition]{Definition}
\aliascntresetthe{Definition}
\crefname{Definition}{definition}{definitions}
\newaliascnt{Proposition}{theorem}
\newtheorem{proposition}[Proposition]{Proposition}
\aliascntresetthe{Proposition}
\crefname{Proposition}{proposition}{propositions}
\newaliascnt{Corollary}{theorem}
\newtheorem{corollary}[Corollary]{Corollary}
\aliascntresetthe{Corollary}
\crefname{Corollary}{corollary}{corrolaries}
\newaliascnt{Fact}{theorem}
\newtheorem{fact}[Fact]{Fact}
\aliascntresetthe{Fact}
\crefname{Fact}{fact}{fatcs}
\newaliascnt{Conjecture}{theorem}
\newtheorem{conjecture}[Conjecture]{Conjecture}
\aliascntresetthe{Conjecture}
\crefname{Conjecture}{conjecture}{conjectures}
\newtheorem*{definition*}{Definition}
\newtheorem*{proposition*}{Proposition}
\newtheorem*{corollary*}{Corollary}
\newtheorem*{fact*}{Fact}
\newtheorem*{conjecture*}{Conjecture}

\theoremstyle{remark}
\newaliascnt{Remark}{theorem}
\newtheorem{remark}[Remark]{Remark}
\aliascntresetthe{Remark}
\crefname{Remark}{remark}{remarks}
\newaliascnt{Example}{theorem}
\newtheorem{example}[Example]{Example}
\aliascntresetthe{Example}
\crefname{Example}{example}{examples}
\newaliascnt{Claim}{theorem}
\newtheorem{claim}[Claim]{Claim}
\aliascntresetthe{Claim}
\crefname{Claim}{claim}{claims}
\newtheorem*{remark*}{Remark}
\newtheorem*{example*}{Example}
\newtheorem*{claim*}{Claim}

\AtBeginEnvironment{definition}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{definition}{\setlist{}}
\AtBeginEnvironment{definition*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{definition*}{\setlist{}}
\AtBeginEnvironment{proposition}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{proposition}{\setlist{}}
\AtBeginEnvironment{proposition*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{proposition*}{\setlist{}}
\AtBeginEnvironment{corollary}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{corollary}{\setlist{}}
\AtBeginEnvironment{corollary*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{corollary*}{\setlist{}}
\AtBeginEnvironment{fact}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{fact}{\setlist{}}
\AtBeginEnvironment{fact*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{fact*}{\setlist{}}
\AtBeginEnvironment{conjecture}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{conjecture}{\setlist{}}
\AtBeginEnvironment{conjecture*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{conjecture*}{\setlist{}}

\AtBeginEnvironment{theorem}{\setlist{font=\upshape, before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{theorem}{\setlist{}}
\AtBeginEnvironment{theorem*}{\setlist{font=\upshape, before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{theorem*}{\setlist{}}
\AtBeginEnvironment{lemma}{\setlist{font=\upshape, before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{lemma}{\setlist{}}
\AtBeginEnvironment{lemma*}{\setlist{font=\upshape, before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{lemma*}{\setlist{}}

\AtBeginEnvironment{remark}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{remark}{\setlist{}}
\AtBeginEnvironment{remark*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{remark*}{\setlist{}}
\AtBeginEnvironment{example}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{example}{\setlist{}}
\AtBeginEnvironment{example*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{example*}{\setlist{}}
\AtBeginEnvironment{claim}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{claim}{\setlist{}}
\AtBeginEnvironment{claim*}{\setlist{before=\leavevmode,topsep=.5\topsep,itemsep=.5\itemsep}}
\AtEndEnvironment{claim*}{\setlist{}}

\renewcommand*{\proofname}{Proof:}

\expandafter\let\expandafter\oldproof\csname\string\proof\endcsname
\let\oldendproof\endproof
\renewenvironment{proof}[1][]{%
	\oldproof[\scshape \IfEq{#1}{}{Proof:}{Proof (#1):}]%
}{\oldendproof}

\AtBeginEnvironment{proof}{\setlist{before=\leavevmode}}
\AtEndEnvironment{proof}{\setlist{}}

\numberwithin{equation}{section}


% *****************************
% ********** FIGURES **********
% *****************************

\RequirePackage{caption}

\captionsetup{
	format=plain,
	justification=centering,
	singlelinecheck=false,
	labelfont=bf,
%	font=normalsize, % This covers labelfont and textfont
	labelsep=period,
	figurename=Figure
}


% **********************************
% ********** BIBLIOGRAPHY **********
% **********************************

\let\OLDthebibliography\thebibliography
\renewcommand\thebibliography[1]{\fontsize{9.5}{12}\selectfont
	\OLDthebibliography{#1}
	\setlength{\parskip}{.2\baselineskip}
	\setlength{\itemsep}{0pt plus 0.3ex}
}

% *******************************
% ********** TITLEPAGE **********
% *******************************

\RequirePackage{titling}
\RequirePackage{datetime}
\RequirePackage{totpages}
\RequirePackage{fancyhdr}
\RequirePackage{setspace}
\RequirePackage{textcase}
\RequirePackage[mathlines]{lineno}
\RequirePackage{footmisc}
\DefineFNsymbols*{mysymbols}[math]{*{**}\S\P\ddagger\#\triangle\triangledown\%}
\setfnsymbol{mysymbols}
\RequirePackage{xargs}


% ***********************************
% ********** EDITORS' PART **********
% ***********************************

% Defining the presenter field

\newcommand{\Presenter}[1]{%
	\gdef\Pres{#1}} % Obligatory argument (possibly empty): the name of a presenting editor
\newcommand{\Pres}{}

%%%%%%%%%%


% Defining the submission date field

\newcommand{\Received}[3]{%
	\gdef\DayR{#1} % Obligatory argument: the day in the submission date (in the format: d or dd)
	\gdef\MonthR{#2} % Obligatory argument: the month in the submission date (in the format: m or mm)
	\gdef\YearR{#3}} % Obligatory argument: the year in the submission date (in the format: yyyy)
\newcommand{\DayR}{}
\newcommand{\MonthR}{}
\newcommand{\YearR}{}

%%%%%%%%%%


% Defining the index-of-the-text-to-be-published field

\newcommand{\Ordinal}[1]{%
	\gdef\Ord{#1}} % Obligatory argument: the position of an accepted paper in the sequence of papers accepted in the current year -- these indices are assigned in the chronological order, starting from 1 in each year
\newcommand{\Ord}{}

%%%%%%%%%%


% Defining the submission date field

\newcommand{\PublishedOnline}[3]{%
	\gdef\DayPO{#1} % Obligatory argument: the day in the online publication date (in the format: d or dd)
	\gdef\MonthPO{#2} % Obligatory argument: the month in the online publication date (in the format: m or mm)
	\gdef\YearPO{#3}} % Obligatory argument: the year in the online publication date (in the format: yyyy)
\newcommand{\DayPO}{}
\newcommand{\MonthPO}{}
\newcommand{\YearPO}{}

%%%%%%%%%%


% Defining the revision date field

\newcommand{\Revised}[3]{%
	\gdef\DayRev{#1} % Obligatory argument: the day in the online publication date (in the format: d or dd)
	\gdef\MonthRev{#2} % Obligatory argument: the month in the online publication date (in the format: m or mm)
	\gdef\YearRev{#3}} % Obligatory argument: the year in the online publication date (in the format: yyyy)
\newcommand{\DayRev}{}
\newcommand{\MonthRev}{}
\newcommand{\YearRev}{}

%%%%%%%%%%


% Defining the acceptance date field

\newcommand{\Accepted}[3]{%
	\gdef\DayAcc{#1} % Obligatory argument: the day in the online publication date (in the format: d or dd)
	\gdef\MonthAcc{#2} % Obligatory argument: the month in the online publication date (in the format: m or mm)
	\gdef\YearAcc{#3}} % Obligatory argument: the year in the online publication date (in the format: yyyy)
\newcommand{\DayAcc}{}
\newcommand{\MonthAcc}{}
\newcommand{\YearAcc}{}

%%%%%%%%%%


% Defining the number of the first page field

\newcommand{\Page}[1]{\setcounter{page}{#1}} % Obligatory argument: the number of the first page

%%%%%%%%%%


% Defining the data of the issue field

\newcommand{\Published}[3]{%
	\gdef\VolumeP{#1}  % Obligatory argument: the volume of the issue (in the format: vv)
	\gdef\NumberP{#2}  % Obligatory argument: the number of the issue (in the format: n)
	\gdef\YearP{#3}}  % Obligatory argument: the year of the issue (in the format: yyyy)
\newcommand{\DayP}{}
\newcommand{\MonthP}{}
\newcommand{\YearP}{}

%%%%%%%%%%


% Defining the author header abbreviation field

\newcommand{\AuthAbbrv}[1]{
	\gdef\AuthHead{#1}} % Obligatory argument (possibly empty): the way the author header should be abbreviated: (a) F. Author, S. Author, T. Author (argument: `a') or (b) First Author \textit{et al.} (argument: `b')
\newcommand{\AuthHead}{}

%%%%%%%%%%


% ***********************************
% ********** AUTHORS' PART **********
% ***********************************

% Defining the author-email command

\newcounter{authcount}

\newcommandx{\AuthorEmail}[6][1=0,3=0,5=0,usedefault]{
	\stepcounter{authcount}
	\expandafter\gdef\csname orcid\Alph{authcount}\endcsname{#1} % Optional argument: an author's orcid
	\expandafter\gdef\csname auth\Alph{authcount}\endcsname{#2} % Obligatory argument: an author's name
	\expandafter\gdef\csname authabbr\Alph{authcount}\endcsname{#3} % Optional argument: an author's abbreviated name
	\expandafter\gdef\csname email\Alph{authcount}\endcsname{#4} % Obligatory argument: an author's email
	\expandafter\gdef\csname thanks\Alph{authcount}\endcsname{\unexpanded{#5}} % Optional argument: the text of an author's thanks
	\expandafter\gdef\csname share\Alph{authcount}\endcsname{#6} % Obligatory argument: an author's percentage share in preparing the paper
	 % Generating the abbreviated form of an author's name: initial of the first name + surname
}

%%%%%%%%%%


%Defining the affiliation command

\newcounter{affilcount}

\newcommand{\Affiliation}[5]{
	\stepcounter{affilcount}
	\expandafter\gdef\csname university\Alph{affilcount}\endcsname{#1} % Obligatory argument (possibly empty): the name of a university / institution
	\expandafter\gdef\csname department\Alph{affilcount}\endcsname{#2} % Obligatory argument (possibly empty): the name of a department / institute / faculty
	\expandafter\gdef\csname address\Alph{affilcount}\endcsname{#3} % Obligatory argument (possibly empty): work address
	\expandafter\gdef\csname town\Alph{affilcount}\endcsname{#4} % Obligatory argument (possibly empty): the name of a town and country of the institution
	\expandafter\gdef\csname assign\Alph{affilcount}\endcsname{#5} % Obligatory argument: indices of the authors assigned to the affiliation
	}

%%%%%%%%%%


%Defining the title command

\newcommandx{\Title}[3][1=0,3=0,usedefault]{
	\gdef\titlabbr{\unexpanded{#1}} % Optional argument: the title in an abbreviated form to be displayed in the header
	\gdef\titl{\unexpanded{#2}} % Obligatory argument: the title to be displayed on the title page
	\gdef\titlthanks{\unexpanded{#3}}} % Optional argument: the text of the title thanks
\newcommand{\titlthanks}{}
\newcommand{\titl}{}
\newcommand{\titlabbr}{}

%%%%%%%%%%


%Defining the funding, conflict of interests, ethics, share, and use of GAI tools commands

\newcommand{\Funding}[1]{% obligatory argument -- funding information
	\gdef\fund{#1}}
\newcommand{\fund}{}

\newcommand{\Ethics}[1]{% obligatory argument -- ethical considerations
	\gdef\ethics{#1}}
\newcommand{\ethics}{}

\newcommand{\Conflict}[1]{% obligatory argument -- conflict of interests
	\gdef\conflict{#1}}
\newcommand{\conflict}{}

\newcommand{\UseOfGAI}[1]{% obligatory argument -- use of General Artificial Intelligence tools
	\gdef\GAI{#1}}
\newcommand{\GAI}{}


% Building full author header

\newcounter{authheadc}
\gdef\authorheaderc{
	\addtocounter{authcount}{-1}
	\@whilenum\value{authheadc}<\value{authcount}\do{%
		\stepcounter{authheadc}%
		\csname auth\Alph{authheadc}\endcsname, %
	}%
	\stepcounter{authcount}%
	\csname auth\Alph{authcount}\endcsname%
	\setcounter{authheadc}{0}
}

%%%%%%%%%%


% Building abbreviated author header

\newcounter{authheada}
\gdef\authorheadera{
	\addtocounter{authcount}{-1}
	\@whilenum\value{authheada}<\value{authcount}\do{%
		\stepcounter{authheada}%
		\IfEq{\csname authabbr\Alph{authheada}\endcsname}{0}{\csname auth\Alph{authheada}\endcsname}{\csname authabbr\Alph{authheada}\endcsname}, %
	}%
	\stepcounter{authcount}%
	\csname authabbr\Alph{authcount}\endcsname%
	\setcounter{authheada}{0}
}

%%%%%%%%%%


% Building alternative abbreviated author header

\gdef\authorheaderb{
\authA{} \textit{et al.}
}

%%%%%%%%%%


% Determining headers and building affiliation blocks

\RequirePackage{afterpage}

\AtBeginDocument{
	
	\label{FirstPage}
	
	% Building affiliation blocks
	
	\newcounter{noteend}
	
	\@whilenum\value{noteend}<\value{affilcount}\do{
		\stepcounter{noteend}
		\expandafter\gdef\csname affil\Alph{noteend}\endcsname{%
			\csname university\Alph{noteend}\endcsname
			
			\csname department\Alph{noteend}\endcsname
			
			\csname address\Alph{noteend}\endcsname
			
			\csname town\Alph{noteend}\endcsname
		}
	}
	
	\setcounter{noteend}{0}
	
	%%%%%%%%%%
	
	
	% Determining the headers
	
	\bgroup
	\renewcommand{\\}{ }
	
	\StrSubstitute{\titl}{\space\space}{\space}[\titlenobreakaux]
	\StrSubstitute{\titlenobreakaux}{\space\space}{\space}[\titlenobreak]
	
	\IfEq{\titlabbr}{0}{\gdef\titlehead{\titlenobreak}}{\gdef\titlehead{\titlabbr}}
	
	\IfEqCase{\AuthHead}{{a}{\gdef\authhead{\authorheadera}}{b}{\gdef\authhead{\authorheaderb}}}[\gdef\authhead{\authorheaderc}]
	
	\markboth{\upshape\protect\authhead}{\titlehead}
	\egroup
	
	\newcounter{authaux}
	
	\maketitle
	
	%%%%%%%%%%
}

%%%%%%%%%%



% *****************************************
% ********** OPTION `MANUSCRIPT' **********
% *****************************************

\DeclareOption{manuscript}{
	\PassOptionsToPackage{allcolors=blue}{hyperref}
	\thispagestyle{fancy}
	\pagestyle{myheadings}
	\fancyhf{}
		
	% Defining the footer on the title page
	
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[L]{\footnotesize{\phantom{{\bfseries Presented by:}}\textcolor{white}{.}\\
			\phantom{{\bfseries Received}:}\textcolor{white}{.}\\
			\phantom{{\bfseries Received in revised form}:}\textcolor{white}{.}\\
			\phantom{{\bfseries Accepted}:}\textcolor{white}{.}\\
			\phantom{{\bfseries Published online}:}\\[.5\baselineskip]
			\copyright{} Copyright by the Author(s), \the\year{}\\
			\phantom{Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland}\textcolor{white}{.}\\[2pt]
			\phantom{\begin{minipage}[t]{.13\linewidth}
					\href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
					\end{minipage}
					\begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
					\end{minipage}}}
	}

		\linenumbers
		
	%%%%%%%%%%
		
		
	% Reshaping the title page

	\renewcommand\maketitle{
		
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
			
			{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic
				
				\phantom{{\bfseries Published online}:}
				
				\phantom{\url{https://doi.org/10.18778/0138-0680}}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo}}
		\end{minipage}\bigskip
		
		\bgroup
		\renewcommand{\thefootnote}{\fnsymbol{footnote}}
			\setstretch{1.25}
			
		\@whilenum\value{authaux}<\value{authcount}\do{
			\stepcounter{authaux}
	
			\noindent\csname auth\Alph{authaux}\endcsname{}{\noexpandarg\IfEq{\csname thanks\Alph{authaux}\endcsname}{0}{}{\footnote{\csname thanks\Alph{authaux}\endcsname}}} {\noexpandarg\IfEq{\csname orcid\Alph{authaux}\endcsname}{0}{}{\href{http://orcid.org/\csname orcid\Alph{authaux}\endcsname}{\includegraphics[height=.6\baselineskip]{orcid_logo}}}}
	
		}
		\setcounter{authaux}{0}
		\vspace{2\baselineskip}

		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		\egroup
		\setcounter{footnote}{0}
		}
		
	
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
		\bigskip
		
		\noindent\framebox[\linewidth]{\centering\bigskip
			
			\begin{minipage}{.95\linewidth}
				\noindent\textbf{Funding information:} \fund\smallskip
				
				\noindent\textbf{Conflict of interests:} \conflict\smallskip
				
				\noindent\textbf{Ethical considerations:} \ethics\smallskip
				
				\noindent\textbf{The percentage share of the author in the preparation of the work:}%
				%
				\makeatletter%
				%
				\newcounter{sharecount}%
				%
				\addtocounter{authcount}{-1}%
				%
				\@whilenum\value{sharecount}<\value{authcount}\do{
					\stepcounter{sharecount}%
					\csname auth\Alph{sharecount}\endcsname: \csname share\Alph{sharecount}\endcsname\%, 
				}\makeatother%
				%
				\stepcounter{authcount}%
				%
				\ \csname auth\Alph{authcount}\endcsname: \csname share\Alph{authcount}\endcsname\%%
				\smallskip
				
				\noindent\textbf{Declaration regarding the use of GAI tools:} \GAI
			\end{minipage}
		}
		
	}
	
	%%%%%%%%%%
}

%%%%%%%%%%


% *************************************
% ********** OPTION `ONLINE' **********
% *************************************

\DeclareOption{online}{
	\thispagestyle{fancy}
	\pagestyle{myheadings}
	\fancyhf{}
	
	% Defining the footer on the title page
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[L]{\footnotesize{{\bfseries Presented by}: \Pres{}\\
		   {\bfseries Received}: \monthname[\MonthR] \DayR, \YearR{}\\
		   {\bfseries Received in revised form}: \monthname[\MonthRev] \DayRev, \YearRev{}\\
		   {\bfseries Accepted}: \monthname[\MonthAcc] \DayAcc, \YearAcc{}\\
	  	   \phantom{{\bfseries Published online}:}\\[.5\baselineskip]
	  	   \copyright{} Copyright by the Author(s), \YearPO{}\\
	  	   Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland\\[2pt]
	  	   \begin{minipage}[t]{.13\linewidth}
	  	   \href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
	  	   \end{minipage}
	  	   \begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
	  	   \end{minipage}}
	}
	
	\pagenumbering{gobble}
	
	%%%%%%%%%%
	
	
	% Reshaping the title page
    
	\renewcommand\maketitle{
		
		\newgeometry{asymmetric,%
			top=15pc,%
			left=12pc,%
			height=28\baselineskip,%
			textwidth=27pc,%
			includefoot%
		}
	
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
		{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic

   	 {\bfseries Published online}: \monthname[\MonthPO] \DayPO, \YearPO; \ref*{TotPages} pages

		\url{https://doi.org/10.18778/0138-0680.\YearPO.\Ord}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo}}
		\end{minipage}\bigskip
	
	
		\bgroup
		\renewcommand{\thefootnote}{\fnsymbol{footnote}}
		\setstretch{1.25}
	
		\@whilenum\value{authaux}<\value{authcount}\do{
		\stepcounter{authaux}
		
		\noindent\csname auth\Alph{authaux}\endcsname{}{\noexpandarg\IfEq{\csname thanks\Alph{authaux}\endcsname}{0}{}{\footnote{\csname thanks\Alph{authaux}\endcsname}}} {\noexpandarg\IfEq{\csname orcid\Alph{authaux}\endcsname}{0}{}{\href{http://orcid.org/\csname orcid\Alph{authaux}\endcsname}{\includegraphics[height=.6\baselineskip]{orcid_logo}}}}
		
		}
		\setcounter{authaux}{0}
		\egroup
		\setcounter{footnote}{0}
		\vspace{2\baselineskip}
	
		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		
		\afterpage{\globaldefs=1 \restoregeometry}
	}
	
	
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
		\bigskip
		
		\noindent\framebox[\linewidth]{\centering\bigskip
			
			\begin{minipage}{.95\linewidth}
				\noindent\textbf{Funding information:} \fund\smallskip
				
				\noindent\textbf{Conflict of interests:} \conflict\smallskip
				
				\noindent\textbf{Ethical considerations:} \ethics\smallskip
				
				\noindent\textbf{The percentage share of the author in the preparation of the work:}%
				%
				\makeatletter%
				%
				\newcounter{sharecount}%
				%
				\addtocounter{authcount}{-1}%
				%
				\@whilenum\value{sharecount}<\value{authcount}\do{
					\stepcounter{sharecount}%
					\csname auth\Alph{sharecount}\endcsname: \csname share\Alph{sharecount}\endcsname\%, 
				}\makeatother%
				%
				\stepcounter{authcount}%
				%
				\ \csname auth\Alph{authcount}\endcsname: \csname share\Alph{authcount}\endcsname\%%
				\smallskip
				
				\noindent\textbf{Declaration regarding the use of GAI tools:} \GAI
			\end{minipage}
		}
		
	}
	
	%%%%%%%%%%
}

%%%%%%%%%%


% ************************************
% ********** OPTION `FINAL' **********
% ************************************

\DeclareOption{final}{
	\pagestyle{myheadings}
	\thispagestyle{fancy}
	\fancyhf{}
	
	
	% Defining the footer on the title page
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[L]{\footnotesize{{\bfseries Presented by}: \Pres{}\\
				{\bfseries Received}: \monthname[\MonthR] \DayR, \YearR{}\\
				{\bfseries Received in revised form}: \monthname[\MonthRev] \DayRev, \YearRev{}\\
				{\bfseries Accepted}: \monthname[\MonthAcc] \DayAcc, \YearAcc{}\\
				{\bfseries Published online}: \monthname[\MonthPO] \DayPO, \YearPO\\[.5\baselineskip]
				\copyright{} Copyright by the Author(s), \YearPO{}\\
				Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland\\[2pt]
				\begin{minipage}[t]{.13\linewidth}
					\href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
				\end{minipage}
				\begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
				\end{minipage}}
	}

	%%%%%%%%%%


	% Reshaping the title page
		
	\renewcommand\maketitle{
		
		\newgeometry{asymmetric,%
			top=15pc,%
			left=12pc,%
			height=28\baselineskip,%
			textwidth=27pc,%
			includefoot%
		}
		
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
			{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic
				
				Volume \VolumeP/\NumberP{} (\YearP), pp. \pageref{FirstPage}--\pageref{TotPages}
				
				\url{https://doi.org/10.18778/0138-0680.\YearPO.\Ord}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo}}
		\end{minipage}\bigskip
		
		
		\bgroup
		\renewcommand{\thefootnote}{\fnsymbol{footnote}}
		\setstretch{1.25}
		
		\@whilenum\value{authaux}<\value{authcount}\do{
			\stepcounter{authaux}
			
			\noindent\csname auth\Alph{authaux}\endcsname{}{\noexpandarg\IfEq{\csname thanks\Alph{authaux}\endcsname}{0}{}{\footnote{\csname thanks\Alph{authaux}\endcsname}}}  {\noexpandarg\IfEq{\csname orcid\Alph{authaux}\endcsname}{0}{}{\href{http://orcid.org/\csname orcid\Alph{authaux}\endcsname}{\includegraphics[height=.6\baselineskip]{orcid_logo}}}}
			
		}
		\setcounter{authaux}{0}
		\egroup
		\setcounter{footnote}{0}
		\vspace{2\baselineskip}
		
		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		
		\afterpage{\globaldefs=1 \restoregeometry}
	}
	
	
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
		\bigskip
		
		\noindent\framebox[\linewidth]{\centering\bigskip
			
			\begin{minipage}{.95\linewidth}
				\noindent\textbf{Funding information:} \fund\smallskip
				
				\noindent\textbf{Conflict of interests:} \conflict\smallskip
				
				\noindent\textbf{Ethical considerations:} \ethics\smallskip
				
				\noindent\textbf{The percentage share of the author in the preparation of the work:}%
				%
				\makeatletter%
				%
				\newcounter{sharecount}%
				%
				\addtocounter{authcount}{-1}%
				%
				\@whilenum\value{sharecount}<\value{authcount}\do{
					\stepcounter{sharecount}%
					\csname auth\Alph{sharecount}\endcsname: \csname share\Alph{sharecount}\endcsname\%, 
				}\makeatother%
				%
				\stepcounter{authcount}%
				%
				\ \csname auth\Alph{authcount}\endcsname: \csname share\Alph{authcount}\endcsname\%%
				\smallskip
				
				\noindent\textbf{Declaration regarding the use of GAI tools:} \GAI
			\end{minipage}
		}
		
	}

	%%%%%%%%%%
}

%%%%%%%%%%


% ******************************************
% ********** OPTION `FINAL-PRINT' **********
% ******************************************

\DeclareOption{final-print}{
	\hypersetup{colorlinks=false}
	\pagestyle{myheadings}
	\thispagestyle{fancy}
	\fancyhf{}
	
	
	% Defining the footer on the title page
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[L]{\footnotesize{{\bfseries Presented by}: \Pres{}\\
				{\bfseries Received}: \monthname[\MonthR] \DayR, \YearR{}\\
				{\bfseries Received in revised form}: \monthname[\MonthRev] \DayRev, \YearRev{}\\
				{\bfseries Accepted}: \monthname[\MonthAcc] \DayAcc, \YearAcc{}\\
				{\bfseries Published online}: \monthname[\MonthPO] \DayPO, \YearPO\\[.5\baselineskip]
				\copyright{} Copyright by the Author(s), \YearPO{}\\
				Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland\\[2pt]
				\begin{minipage}[t]{.13\linewidth}
					\href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
				\end{minipage}
				\begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
				\end{minipage}}
	}
	
	%%%%%%%%%%
	
	
	% Reshaping the title page
	
	\renewcommand\maketitle{
		
		\newgeometry{asymmetric,%
			top=15pc,%
			left=12pc,%
			height=28\baselineskip,%
			textwidth=27pc,%
			includefoot%
		}
		
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
			{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic
				
				Volume \VolumeP/\NumberP{} (\YearP), pp. \pageref{FirstPage}--\pageref{TotPages}
				
				\url{https://doi.org/10.18778/0138-0680.\YearPO.\Ord}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo_bw}}
		\end{minipage}\bigskip
		
		
		\bgroup
		\renewcommand{\thefootnote}{\fnsymbol{footnote}}
		\setstretch{1.25}
		
		\@whilenum\value{authaux}<\value{authcount}\do{
			\stepcounter{authaux}
			
			\noindent\csname auth\Alph{authaux}\endcsname{}{\noexpandarg\IfEq{\csname thanks\Alph{authaux}\endcsname}{0}{}{\footnote{\csname thanks\Alph{authaux}\endcsname}}}  {\noexpandarg\IfEq{\csname orcid\Alph{authaux}\endcsname}{0}{}{\includegraphics[height=.6\baselineskip]{orcid_logo_bw}\,{\tiny\raisebox{.22\baselineskip}{https://orcid.org/\csname orcid\Alph{authaux}\endcsname}}}}
			
		}
		\setcounter{authaux}{0}
		\egroup
		\setcounter{footnote}{0}
		\vspace{2\baselineskip}
		
		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		
		\afterpage{\globaldefs=1 \restoregeometry}
	}
	
	
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
		\bigskip
		
		\noindent\framebox[\linewidth]{\centering\bigskip
			
			\begin{minipage}{.95\linewidth}
				\noindent\textbf{Funding information:} \fund\smallskip
				
				\noindent\textbf{Conflict of interests:} \conflict\smallskip
				
				\noindent\textbf{Ethical considerations:} \ethics\smallskip
				
				\noindent\textbf{The percentage share of the author in the preparation of the work:}%
				%
				\makeatletter%
				%
				\newcounter{sharecount}%
				%
				\addtocounter{authcount}{-1}%
				%
				\@whilenum\value{sharecount}<\value{authcount}\do{
					\stepcounter{sharecount}%
					\csname auth\Alph{sharecount}\endcsname: \csname share\Alph{sharecount}\endcsname\%, 
				}\makeatother%
				%
				\stepcounter{authcount}%
				%
				\ \csname auth\Alph{authcount}\endcsname: \csname share\Alph{authcount}\endcsname\%%
				\smallskip
				
				\noindent\textbf{Declaration regarding the use of GAI tools:} \GAI
			\end{minipage}
		}
		
	}
	
	%%%%%%%%%%
}

%%%%%%%%%%


% ****************************************
% ********** OPTION `EDITORIAL' **********
% ****************************************

\DeclareOption{editorial}{
	\pagestyle{myheadings}
	\thispagestyle{fancy}
	\fancyhf{}
	
	
	% Defining the footer on the title page
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[C]{\footnotesize{\copyright{} Copyright by the Author(s), \YearP{}\\
				Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland\\[2pt]
				\begin{minipage}[t]{.13\linewidth}
					\href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
				\end{minipage}
				\begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
				\end{minipage}}
	}
	
	%%%%%%%%%%
	
	
	% Reshaping the title page
	
	\renewcommand\maketitle{
		
		\newgeometry{asymmetric,%
			top=15pc,%
			left=12pc,%
			height=33\baselineskip,%
			textwidth=27pc,%
			includefoot%
		}
		
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
			{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic
				
				Volume \VolumeP/\NumberP{} (\YearP), pp. \pageref{FirstPage}--\pageref{TotPages}
				
				\url{https://doi.org/10.18778/0138-0680.\YearP.\Ord}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo}}
		\end{minipage}\bigskip
		
		
		\setcounter{footnote}{0}
		\vspace{2\baselineskip}
		
		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		
		\afterpage{\globaldefs=1 \restoregeometry}
	}
	
	
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
	
	}
	
	%%%%%%%%%%
}

%%%%%%%%%%


% **********************************************
% ********** OPTION `EDITORIAL-PRINT' **********
% **********************************************

\DeclareOption{editorial-print}{
	\hypersetup{colorlinks=false}
	\pagestyle{myheadings}
	\thispagestyle{fancy}
	\fancyhf{}
	
	
	% Defining the footer on the title page
	
	\renewcommand\headrulewidth{0pt}
	\renewcommand\footrulewidth{0.5pt}
	\renewcommand\footrule{
		\kern 10pt
		\hrule width \textwidth height 1pt
		\kern 3pt
	}
	\fancyfoot[L]{\footnotesize{\copyright{} Copyright by the Author(s), \YearP{}\\
				Licensee Lodz University -- Lodz University Press, {\L}{\'o}d{\'z}, Poland\\[2pt]
				\begin{minipage}[t]{.13\linewidth}
					\href{https://creativecommons.org/licenses/by-nc-nd/4.0/}{\includegraphics[height=1.5\baselineskip]{CC_BY-NC-ND}}
				\end{minipage}
				\begin{minipage}[b]{.85\linewidth}This article is an open access article distributed under the terms and conditions of the Creative Commons Attribution license CC-BY-NC-ND 4.0.
				\end{minipage}}
	}
	
	%%%%%%%%%%
	
	
	% Reshaping the title page
	
	\renewcommand\maketitle{
		
		\newgeometry{asymmetric,%
			top=15pc,%
			left=12pc,%
			height=33\baselineskip,%
			textwidth=27pc,%
			includefoot%
		}
		
		\noindent\begin{minipage}[c]{0.7\linewidth}\setstretch{1.25}
			{\footnotesize \textbf{B}ulletin of the \textbf{S}ection of \textbf{L}ogic
				
				Volume \VolumeP/\NumberP{} (\YearP), pp. \pageref{FirstPage}--\pageref{TotPages}
				
				\url{https://doi.org/10.18778/0138-0680.\YearP.\Ord}}
		\end{minipage}%
		\hfill%
		\begin{minipage}[c]{0.25\linewidth}
			\hfill\href{https://publicationethics.org/}{\includegraphics[height=1.8cm]{cope_logo_bw}}
		\end{minipage}\bigskip
		
		
		\setcounter{footnote}{0}
		\vspace{2\baselineskip}
		
		\begin{center}
			\begin{minipage}{0.9\linewidth}
				\begin{center}
					\begin{spacing}{1.25}
						\bgroup
						\renewcommand{\\}{\break}			
						{\large\MakeTextUppercase{\titl}{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotemark}}}
						\egroup
					\end{spacing}
				\end{center}
			\end{minipage}
		\end{center}
		{\noexpandarg\IfEq{\titlthanks}{0}{}{\footnotetext{\titlthanks}}}
		
		\afterpage{\globaldefs=1 \restoregeometry}
	}
	
		
	% Information about the authors at the end of the paper
	
	\AtEndDocument{
		
		\makeatletter
		
		\newcounter{endnote}
		
		\@whilenum\value{endnote}<\value{authcount}\do{
			\stepcounter{endnote}
			\bigskip
			
			\noindent\begin{minipage}{\linewidth}
				{\bfseries\csname auth\Alph{endnote}\endcsname}\smallskip
				
				\@whilenum\value{noteend}<\value{affilcount}\do{
					\stepcounter{noteend}
					\IfSubStr{\csname assign\Alph{noteend}\endcsname}{\arabic{endnote}}{\csname affil\Alph{noteend}\endcsname\smallskip
						
					}{}
				}
				\setcounter{noteend}{0}
				
				\IfEq{\csname email\Alph{endnote}\endcsname}{}{}{e-mail: \url{\csname email\Alph{endnote}\endcsname}}%
			\end{minipage}%
		}\makeatother%
		
	}
	
	%%%%%%%%%%
}

%%%%%%%%%%

\ProcessOptions\relax


% *******************************************
% ********** ABSTRACT AND KEYWORDS **********
% *******************************************

\RequirePackage{environ}

% Defining the abstract field

\renewenvironment{abstract}
{
	\begin{center}
		\bfseries\fontsize{9}{9}\selectfont \abstractname
	\end{center}
\bgroup
	\setstretch{1.25}%
	\fontsize{9}{9}\selectfont%
}
{\egroup}

%%%%%%%%%%


% Defining the keywords field

\NewEnviron{keywords}%
	{\medskip\par	
		\bgroup%
		\setstretch{1.5}%
		\fontsize{9}{9}\selectfont%
		\noindent{\em Keywords}: %
		\BODY
	\unskip.\egroup}

%%%%%%%%%%


% Defining the Mathematical Classification Subject fields

\newenvironment{msc}[1][2010]
	{\medskip\par
		\bgroup%
		\setstretch{1.5}%
		\fontsize{9}{9}\selectfont%
		{\em\noindent#1{} Mathematical Subject Classification}:%
	}
	{\unskip.\egroup}


%%%%%%%%%%


% **************************************
% ********** ACKNOWLEDGEMENTS **********
% **************************************

\newcommand{\Acknowledgements}{\paragraph{Acknowledgements.}}
