% List of symbols
\addcontentsline{toc}{part}{Index of symbols}
\chapter*{Index of symbols}

% Shorthand for \pageref, we have lots of these.
\newcommand{\pg}[1]{p.~\pageref{#1}}
% In the next macro whitespace matters, so be careful
\newcommand{\symbolindex}[2]{\hbox{\makebox[0.2\textwidth][s]{#1\hfill}\hspace*{2.5em}\parbox[t]{0.65\textwidth}{#2\hfill}}\\[1.5pt]}

% The entries in this table are sorted "alphabetically" whatever that means.

%{\OPTindexfont % Set same font size as for the index

% MAKE SURE THERE ARE NO EMPTY LINES, OR ELSE WE GET A PARAGRAPH BREAK.
% ALSO, DO NOT INSERT ANY WHITESPACE AT THE BEGINNING OF ARGUMENTS OF \symbolindex
\noindent
\symbolindex{ |asdf|}{propositional equality}