\documentclass{beamer}

%include slides.fmt

\usepackage[T1]{fontenc}

\usetheme{Madrid}
\usecolortheme{dolphin}
\setbeamertemplate{navigation symbols}{} 
\usepackage{appendixnumberbeamer}

\title[HoTT and erasing propositions]{Programming in homotopy type theory and erasing propositions}
\institute[Utrecht University]{Department of Information and Computing
  Sciences\\Faculty of Science, Utrecht University}

\author[G. Dijkstra]{Gabe Dijkstra}

\date{\today}

\newcommand{\homotopybetweenpaths}[1]{%
\begin{frame}\frametitle{|J| versus |K|}%
  \begin{figure}%
    \centering%
    \includegraphics[width=0.4\textwidth]{../thesis/img/homotopy#1.pdf}%
  \end{figure}%
\end{frame}%
}

\newcommand{\jvsk}[1]{%
\begin{frame}\frametitle{|J| versus |K|}%
  \begin{figure}%
    \centering%
    \minipage{0.4\textwidth}%
    \includegraphics[width=\textwidth]{../thesis/img/J#1.pdf}%
    \endminipage%
    \hfill%
    \minipage{0.4\textwidth}%
    \includegraphics[width=\textwidth]{../thesis/img/K#1.pdf}%
    \endminipage%
  \end{figure}%
\end{frame}%
}

%include commands.lhs

\begin{document}


\begin{frame}
\maketitle
\end{frame}

\section{Homotopy between paths}

\homotopybetweenpaths{0}
\homotopybetweenpaths{1}
\homotopybetweenpaths{2}
\homotopybetweenpaths{3}

\section{|J| versus |K|}

\jvsk{0}
\jvsk{1}
\jvsk{2}

\end{document}
