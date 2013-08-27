\documentclass{beamer}

%include slides.fmt

\usepackage{xspace}


\usetheme{Madrid}
\usecolortheme{dolphin}
\setbeamertemplate{navigation symbols}{} 
\usepackage{appendixnumberbeamer}
\usepackage[text width=10cm]{todonotes}
\usepackage[T1]{fontenc}
\usepackage[utf8x]{inputenc}
\usepackage{amsmath,amsthm,amssymb,stmaryrd}
\usepackage{tgpagella}

\title[HoTT and erasing propositions]{Programming in homotopy type theory and erasing propositions}
\institute[Utrecht University]{Department of Information and Computing
  Sciences\\Faculty of Science, Utrecht University}

\author[G. Dijkstra]{Gabe Dijkstra}

\date{\today}

\newcommand{\homotopybetweenpaths}[1]{%
\begin{frame}\frametitle{Homotopy between paths}%
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

\begin{frame}{\MLTT}
  \begin{itemize}
  \item Can be seen as:
    \begin{itemize}
    \item Logic to do formal mathematics in
    \item Can be seen as a programming language
    \end{itemize}
  \item Agda is an implementation of \MLTT extended with pattern matching
  \item \MLTT does not have pattern matching, but elimination principles
  \end{itemize}
\end{frame}

\begin{frame}{Introduction \hott}
  \begin{itemize}
  \item \Hott studies propositional equality in (intensional) \MLTT
  \item Propositional equality in type theory is a difficult concept:
    \begin{itemize}
    \item Intensional \MLTT
      \begin{itemize}
      \item Cannot derive function extensionality (|(f g : A -> B) -> ((x : A) -> f x == g x) -> f == g|)
      \item Type checking is decidable
      \end{itemize}
    \item Extensional \MLTT
      \begin{itemize}
      \item Can derive function extensionality
      \item Type checking is undecidable
      \end{itemize}
    \item Heterogeneous equality
    \item Observational type theory
    \end{itemize}

  \end{itemize}
\end{frame}

\begin{frame}{Introduction \hott}
  \begin{itemize}
  \item Interpret an equality |p : x == y| as a path in a topological space
  \item Special year at IAS in Princeton: book
    \begin{itemize}
    \item Focus on formalising mathematics
    \item Aimed at mathematicians unfamiliar with type theory
    \end{itemize}
  \end{itemize}
\end{frame}


\begin{frame}{Research question}
  \begin{center}
    What is \hott and why is interesting \\ to do programming in?
  \end{center}
\end{frame}

\begin{frame}{Homotopy theory}
  \begin{itemize}
  \item \emph{Topology}: study of spaces and \emph{continuous maps} between them
  \item \emph{Homotopy}: study of \emph{continuous deformations} in topological spaces
  \item Continuous deformation of point |x| into |y| is a continuous function:
    |p : [0,1] -> A| \st |p 0 = x| and |p 1 = y|
  \item Continuous deformations have an interesting structure:
    \begin{itemize}
    \item There is a constant deformation
    \item Can be composed
    \item Can be inverted
    \end{itemize}
  \item They form a groupoid \emph{up to homotopy}
  \end{itemize}
\end{frame}

\begin{frame}{Identity types}
  \begin{code}
    data Id (A : Universe) (x : A) : (y : A) -> Universe where
      refl : Id A x x
  \end{code}
      
  \begin{code}
    J  :  (A : Universe)
       ->  (x : A)
       ->  (P : (y : A) -> (p : Id A x y) -> Universe)
       ->  (c : P x x refl)
       ->  (y : A) -> (p : Id A x y)
       ->  P x y p
  \end{code}
\end{frame}

\begin{frame}{Identity types}
  \begin{code}
    data Id (A : Universe) (x : A) : (y : A) -> Universe where
      refl : Id A x x
  \end{code}
  
  \vfill
  
  |Id A x y| forms an equivalence relation:
      
  \begin{itemize}
  \item |refl   : Id A x x|
  \item |symm   : Id A x y -> Id A y x|
  \item |trans  : Id A x y -> Id A y z -> Id A x z|
  \end{itemize}

  |Id A x y| is also a groupoid \emph{up to propositional equality}
\end{frame}

\begin{frame}{Uniqueness of identity proofs}
  \begin{itemize}
  \item |Id| has only one constructor: |refl|
  \item Shouldn't all terms of type |Id A x y| be equal to eachother?
  \end{itemize}

  \begin{code}
    UIP : (A : Universe) (x y : A) (p q : Id A x y) -> Id (Id A x y) p q
    UIP A x dotx refl refl = refl
  \end{code}
  
  \begin{itemize}
  \item Can we prove this using |J|?
  \end{itemize}
\end{frame}

\begin{frame}{|J| versus |K|}
  \begin{code}
    J  :  (A : Universe)
       ->  (x : A)
       ->  (P : (y : A) -> (p : Id A x y) -> Universe)
       ->  (c : P x x refl)
       ->  (y : A) -> (p : Id A x y)
       ->  P x y p
  \end{code}

  \begin{code}
   K  :   (A : Universe) (x : A) (P : Id A x x -> Universe)
      ->  P refl
      ->  (c : Id A x x)
      ->  P c
  \end{code}

\end{frame}

\begin{frame}{\hprops and \hsets}
  \begin{itemize}
  \item In homotopy theory we classify spaces along their homotopy
    groupoids
  \item In \hott we can classify types along their identity types
  \item Contractible type: |Sigma (center : A) dot ((x : A) -> Id A center x)|
    \begin{itemize}
    \item Example: |top|
    \end{itemize}
  \item \hprop: |(x y : A) -> isContractible (Id A x y)|
    \begin{itemize}
    \item Examples: |top| and |bottom|
    \item Satisfies \emph{proof irrelevance}: |(x y : A) -> x == y|
    \end{itemize}
  \item \hset: |(x y : A) -> isprop (Id A x y)|
    \begin{itemize}
    \item Example: |Bool|
    \item Satisfies \emph{\UIP}
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{\hprops and \hsets}
  \begin{itemize}
  \item Are there types that are not \hsets, \ie types that violate \UIP?
  \item \Hits
  \end{itemize}

  \begin{code}
    data Circle : Universe where
      base : Circle
    
      loop : base == base
  \end{code}

  \begin{code}
    Circlerec : (B : Set)
       -> (b : B)
       -> (p : b == b)
       -> Circle -> B
  \end{code}
\end{frame}

\begin{frame}{Univalence}
  \begin{itemize}
  \item Univalence: |(A B : Universe) -> A isomm B -> A == B|
  \item |Type| does not satisfy \uip:
    \begin{itemize}
    \item |refl : Bool == Bool|
    \item |univalence Bool Bool notIso : Bool == Bool|
    \end{itemize}
  \item Univalence implies function extensionality
  \end{itemize}
\end{frame}

\begin{frame}{Applications of \hott}
  \begin{itemize}
  \item Quotient types using \hits
  \item Views for abstract types
  \end{itemize}
\end{frame}

\begin{frame}{Implementation efforts}
  \begin{itemize}
  \item Status quo: use Agda/Coq and postulate the extra equalities
  \item Is sufficient if all you want to do is type checking
  \item Computations get stuck
  \item Computational content of univalence is an open problem
  \item Licata/Harper: canonicity for a restricted version of \hott
    \begin{itemize}
    \item No decidability result for type checking
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Conclusions and future work}
  \emph{What is \hott and why is interesting \\ to do programming in?}

  \begin{itemize}
  \item Giving up pattern matching is a (big) step backwards
  \item \Hits and univalence can become two steps forwards
  \end{itemize}
\end{frame}

\begin{frame}{Erasing propositions}
  \begin{itemize}
  \item When we write certified programs we can distinguish between:
    \begin{itemize}
    \item \emph{proof} (of correctness) parts
    \item \emph{program} parts
    \end{itemize}
  \item The proof parts are only needed during type checking
  \item At run-time we do not want to carry the proof parts around:
    \begin{itemize}
    \item We want to \emph{erase} those parts after type checking
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Erasing propositions}
  \begin{code}
    sort : (xs : List Nat) -> Sigma (ys : List Nat) dot (isSorted xs ys)
  \end{code}

  \begin{itemize}
  \item |isSorted xs ys| is only interesting during type checking
  \item We only care that we have a proof, not what kind of proof it is
    \begin{itemize}
    \item Recall proof irrelevance: |(x y : A) -> x == y|
    \item \hprops
    \end{itemize}
  \item At run-time we want a function |sort' : List Nat -> List Nat|
  \end{itemize}
  
  \vfill

  Can we provide an optimisation based on the concept of \hprops?
\end{frame}

\begin{frame}{Erasing propositions}
  \begin{itemize}
  \item Can't we separate concerns?
    \begin{itemize}
    \item |sort' : List Nat -> List Nat|
    \item |sortCorrect : (xs : List Nat) -> isSorted xs (sort' xs)|
    \end{itemize}
  \item This does not always work:
    \begin{itemize}
    \item |elem : (A : Universe) (xs : List A) (i : Nat) -> i < length xs -> A|
    \item We need |i < length xs| during type checking
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Erasing propositions in Agda}
  \begin{itemize}
  \item In Agda we can mark things as \emph{irrelevant}:
    \begin{code}
      record Sigmairr (A : Universe) (B : A → Universe) : Universe  where
        constructor _,_ 
        field
         fst   : A
         .snd  : B fst
    \end{code}

    \begin{code}
      elem : (A : Universe) (xs : List A) (i : ℕ) → .(i < length xs) → A
    \end{code}
  \item We may not pattern match on irrelevant arguments
  \item Irrelevant arguments may only be passed on to irrelevant contexts
    \begin{itemize}
    \item This prevents us from writing |.A -> A|
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Collapsibility}
\begin{code}
data ltfam : ℕ → ℕ → Universe where
  ltZ : (y : ℕ)            → Z    < S y
  ltS : (x y : ℕ) → x < y  → S x  < S y
\end{code}

with elimination operator

\begin{code}
  ltelim  :  (P : (x y : ℕ) → x < y → Universe)
             (mZ : (y : ℕ) → P 0 (S y) (ltZ y))
             (mS : (x y : ℕ) → (pf : x < y) → P x y pf 
                 → P (S x) (S y) (ltS x y pf))
             (x y : ℕ)
             (pf : x < y)
          →  P x y pf
\end{code}

and computation rules

\begin{code}
  ltelim P mZ mS 0      (S y)  (ltZ y)        =  mZ y
  ltelim P mZ mS (S x)  (S y)  (ltS x y pf)   =  mS x y pf (ltelim P mZ mS x y pf)
\end{code}
\end{frame}

\begin{frame}{Collapsibility}
  \begin{itemize}
  \item A canonical value |p : x < y| is determined completely by its
    indices |x| and |y|
  \item Only way to inspect |p| is via |ltelim|
  \item |ltelim| does not need to inspect |p|
  \item |p| can be erased
  \item When can we do this?
    \begin{itemize}
    \item Collapsible family: given |I : Universe|, |D : I ->
      Universe| is \emph{collapsible} if for every |x, y : D i|:

      \begin{code}
        /- x, y : D i implies /- x === y
      \end{code}

    \end{itemize}
  \item This looks familiar
    \begin{code}
      isprop : (A : Universe) -> Universe
      isprop A = (x y : A) -> x == y
    \end{code}
  \end{itemize}
\end{frame}

\begin{frame}{Internalising collapsibility}
  \begin{itemize}
  \item Collapsibility looks like an indexed version of \hprops
    
  \item Can we \emph{internalise} the collapsibility concept?
    \begin{code}
      isInternallyCollapsible : (I : Universe) (A : I -> Universe) -> Universe
      isInternallyCollapsible I A = (i : I) -> (x y : A i) -> x == y
    \end{code}

  \item Do the two concepts coincide?
    \begin{itemize}
    \item Internal collapsibility implies collapsibility

      if we have |/- p : x == y|, then |p === refl| and |x === y|
    \item The other way around does not hold 
      
      |Id A| is a collapsible family for every |A|, but not internally
      collapsible: we cannot prove \uip
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Internalising the collapsibility optimisation}
  \begin{itemize}
  \item We can internalise the collapsiblity concept: |isInternallyCollapsible|
  \item Can we do the same with the optimisation, \ie can we implement
    the following:
    \begin{code}
      optimiseFunction : 
        (I : Universe) (D : I → Universe) (B : Universe)
        (isInternallyCollapsible I D)
        (f : (i : I) → D i →  B) 
        -> ((i : I) → .(D i) → B)
    \end{code}
  \item Why internalise it in the first place?
    \begin{itemize}
    \item Collapsibility can only be established by the compiler
    \item It is undecidable
    \item Internalising it means the user can provide a proof if the
      compiler fails to do so
    \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Internalising the collapsibility optimisation}
    \begin{code}
      optimiseFunction : 
        (I : Universe) (D : I → Universe) (B : Universe)
        (isInternallyCollapsible I D)
        (f : (i : I) → D i →  B) 
        -> ((i : I) → .(D i) → B)
    \end{code}

    \begin{itemize}
    \item Every |A i| is either empty or isomorphic to |top|
    \item We cannot ``pattern match'' on this fact: type inhabitation is undecidable
    \end{itemize}

    \begin{code}
      isInternallyCollapsibleDecidable : (I : Universe) (D : I -> Universe) -> Universe
      isInternallyCollapsibleDecidable I D = (i : I) 
        -> (((x y : D i) -> x == y) otimes (D i oplus (D i -> bottom)))
    \end{code}
\end{frame}

\begin{frame}{Internalising the collapsibility optimisation}
  \begin{itemize}
  \item If we use |isInternallyCollapsibleDecidable| instead of
    |isInternallyCollapsible|, we can implement |optimiseFunction|
  \item We can also prove its correctness:
    \begin{code}
      optimiseFunctionCorrect :
        (I : Universe) (D : I → Universe) (B : Universe)
        (pf : isInternallyCollapsibleDecidable I D)
        (f : (i : I) → D i →  B)
        (i : I) (x : D i)
        -> optimiseFunction I D B pf f i x == f i x
    \end{code}
  \item Is it actually an optimisation?
  \item |pf| provides us with a function |(i : I) -> D i| that we use to recover the erased value
  \item |pf| is written by the user: no guarantees on its time
    complexity
  \item We can write terms in an |EDSL| that keeps track of time complexity
  \end{itemize}
\end{frame}

\begin{frame}{Internal collapsibility and \hott}
  \begin{itemize}
  \item In ``plain'' \MLTT run-time can be seen as evaluation in the empty context
  \item In \hott we have axioms for the added equalities
  \item Does the optimisation still work?
  \item |optimiseFunctionCorrect| still type checks
  \item but it only establishes \emph{propositional} equality
  \end{itemize}
\end{frame}


\begin{frame}{Internal collapsibility and \hott}
\begin{code}
  data I : Set where
    zero  : Interval
    one   : Interval

    segment : zero == one
\end{code}

with elimination principle

\begin{code}
  Ielim :  (B : Universe)
          -> (b0 : B)
          -> (b1 : B)
          -> (p : b0 == b1)
          -> I -> B
\end{code}

\begin{itemize}
\item |I| is an \hprop
\item Every function |I -> B| is a ``constant'' function (up to propositional equality)
\end{itemize}
\end{frame}

\begin{frame}{Internal collapsibility and \hott}
\begin{code}
  Iid : I -> I
  Iid = Ielim I zero one segment

  Iconstzero : I -> I
  Iconstzero = Ielim I zero zero refl
\end{code}

\begin{itemize}
\item |Iid == Iconstzero|, but they do differ definitionally
  \begin{itemize}
  \item |Iid one === one|
  \item |Iconstzero one === zero|
  \end{itemize}
\item We cannot transform any |f : I -> B| into |fsnake : .I -> B| by
  presupposing the argument to be |zero|
\end{itemize}
\end{frame}

\begin{frame}{Internal collapsibility and \hott}
  \begin{code}
    Ielim :  (B : Universe)
            -> (b0 : B)
            -> (b1 : B)
            -> (p : b0 == b1)
            -> I -> B
  \end{code}


  \begin{itemize}
  \item Sometimes it does work out
  \item Consider functions |f : I -> Bool|
  \item |Bool| only has |refl| paths
  \item We either have for every |i : I| that |f i === True| \\ or we
    have for every |i : I| that |f i === False|
  \item If the |p| argument to |Ielim| is |refl|, it is safe to
    presuppose the |I| argument to be |zero|
  \end{itemize}
\end{frame}

\begin{frame}{Internal collapsibility and \hott}
  \begin{itemize}
  \item Can we always find such a condition?

    \begin{code}
      data nattruncated : Universe where
        0 : nattruncated
        S : (n : nattruncated) -> nattruncated
    
        equalTo0 : (n : nattruncated) -> 0 == n
    \end{code}

    with elimination principle

    \begin{code}
      nattruncatedelim : (B : Universe)
                  -> (b0 : B)
                  -> (bS : B -> B)
                  -> (p : (b : B) -> b0 == b)
                  -> nattruncated -> B
    \end{code}

    \item |nattruncated| is an \hprop
    \item We have to check that for every |b : B| we have |p b === refl|
      \begin{itemize}
      \item This is undecidable
      \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}{Conclusions}
  \begin{itemize}
  \item \emph{Can we provide an optimisation based on the concept of \hprops?}
    \begin{itemize}
    \item In plain \MLTT (with Agda's irrelevance mechanism): yes, if
      we restrict ourselves to decidable \hprops, but time complexity
      is an issue
    \item In \hott: generally not
    \end{itemize}
  \item \emph{Is \hott and why is interesting \\ to do programming in?}
    \begin{itemize}
    \item Yes: we get function extensionality, quotient types, better
      manipulation of isomorphic types via univalence
    \item Not yet: computational content is lacking / we lose pattern
      matching
    \end{itemize}
  \end{itemize}
\end{frame}

\end{document}
