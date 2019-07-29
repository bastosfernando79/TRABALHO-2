%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   taisesantiago@gmail.com
%   Modelo para artigos em Português
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\documentclass[12pt]{article}
\usepackage{geometry}
\usepackage{chngpage}
\usepackage{graphicx}
\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{latexsym}
\usepackage[brazil]{varioref}
\usepackage[english,brazil]{babel}
\geometry{a4paper,left=2.5cm,right=2.5cm,top=2.5cm,bottom=2.5cm}
\usepackage[dvips]{color}
\usepackage[brazilian]{babel}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}


%%%%%%%%%%Definições Teoremas %%%%%%%%%%%%%%%%%%%

 \newtheorem{teo}{Teorema}%[subsection]
 \newtheorem{cor}[teo]{Corolário}
 \newtheorem{lem}[teo]{Lema}
 \newtheorem{prop}[teo]{Proposição}
 \newtheorem{defn}[teo]{Definição}
 \newtheorem{nota}[teo]{Notação}
 \newtheorem{obs}[teo]{Observação}
 \numberwithin{equation}{subsection}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}
\title{O conjunto de Cantor}

\maketitle \abstract{Todo mundo conhece o famoso teorema de
Pitágoras (a soma dos quadrados dos catetos é igual ao quadrado da
hipotenusa, ou simplesmente $ a^2= b^2 + c^2$). O último teorema
de Fermat (veja \cite{CD}) diz que não existem a, b e c inteiros
que satisfaçam a equação $a^n = b^n + c^n$, para nenhum $n > 2$.
Neste trabalho falaremos sobre alguns dos novos campos da
matemática que nasceram com a demonstração feita Andrew Wiles em
1995 com a demonstração da validade de tal teorema.

\medskip

\noindent{\bf Palavras Chave:} Teorema de Fermat,Teorema de
Pitagoras

}

\section*{Introdução}

\section{Conceitos preliminares}
Segue abaixo alguns conceitos fundamentais para entendermos as propriedades do conjunto de Cantor.

\subsection{Conjuntos e Números Reais}

\begin{defn}
    Um conjunto X é dito enumerável se existe uma bijeção f : $\mathbb{N} \rightarrow X$.
\end{defn}

\begin{defn}
    Sejam $a,b \in \mathbb{R}$ com a<b. Então:
    \newline
    \newline
    $[a,b] := \{ x \in \mathbb{R} : a \leq x \leq b\} $
    \newline
    $(a,b] := \{ x \in \mathbb{R} : a < x \leq b\}$
    \newline
    $[a,b) := \{ x \in \mathbb{R} : a \leq x < b\}$
    \newline
    $(a,b) := \{ x \in \mathbb{R} : a < x < b\}$
    \newline
    $(-\infty,b] := \{ x \in \mathbb{R} : x \leq b\}$
    \newline
    $(-\infty,b) := \{ x \in \mathbb{R} : x < b\}$
    \newline
    $[a,+\infty) := \{ x \in \mathbb{R} : x \geq a\}$
    \newline
    $(a,+\infty) := \{ x \in \mathbb{R} : x > a\}$
    \newline
    $[a,a]$ é denominado intervalo degenerado
    
\end{defn}

\begin{defn}
    Seja X um conjunto tal que X $\subset \mathbb{R}$. Dizemos que X é limitado superiormente quando existe b $\in \mathbb{R}$ tal que $x \leq b, \forall x \in X$. Analogamente, dizemos que X $\subset \mathbb{R}$ é limitado inferiormente quando existe a $\in \mathbb{R}$ tal que a $\leq x, \forall x \in X$. O número b chama-se cota superior de X e o número a chama-se cota inferior de X. Se X é limitado superior e inferiormente, dizemos que X é limitado. Isto significa que existe k>0 tal que $|x| \leq k, \forall x \in X$.
\end{defn}


\begin{teo}
    (Intervalos Encaixados) Dada uma sequência decrescente:
    \newline
    $I_1\supset I_2 \supset I_3 \supset ... $ 
    \newline
    de intervalos não-vazios, limitados e fechados: $I_n = [a_n,b_n]$ , existe pelo menos um número c tal que c $\in I_n, \forall n \in \mathbb{N}$.
\end{teo}

\subsection{Noções topológicas em $\mathbb{R}$}

\begin{defn}
    Seja X $\subset \mathbb{R}$.  Um ponto a $\in$ X é um ponto interior de X se existe $\delta$>0 tal que (a-$\delta, a+\delta)\subset$ X.
\end{defn}

\begin{nota}
    O conjunto dos pontos interiores de X será denotado por int(X).
\end{nota}

\begin{defn}
    Seja X $\subset \mathbb{R}$. O conjunto X é aberto quando todos os pontos de X são pontos interiores de X, ou seja, X = int(X).
\end{defn}

\begin{prop}
    Uma união qualquer de abertos é um conjunto aberto, ou seja, se $\{A_\lambda\}_\lambda_\in_L$ é uma família de conjuntos abertos, então $\underset{\lambda\in L}{\bigcup} A_\lambda$ é um conjunto aberto.
\end{prop}

\begin{prop}
    Sejam $A_1, A_2,...,A_N$ subconjuntos abertos de $\mathbb{R}$. Então $\bigcap\limits^N_{i=1}A_i$ é um conjunto aberto. 
\end{prop}

\begin{defn}
    Um conjunto F $\subset \mathbb{R}$ é fechado se, e somente, $F^{c}$ é um conjunto aberto.
\end{defn}

\begin{defn}
    Seja X $\subset \mathbb{R}$. Um ponto a $\in \mathbb{R}$ é um ponto de acumulação de X se para todo $\delta$ > 0, temos (a-$\delta, a+\delta) \cap (X-\{a\})\ne \varnothing$.    
\end{defn}

\begin{nota}
    O conjunto dos pontos de acumulação de X  será denotado por X'. 
\end{nota}

\begin{defn}
    Seja X $\subset \mathbb{R}$. O fecho de X é o conjunto $\overline{X} = X$ $\cup$ X'.
\end{defn}

\begin{defn}
    Seja X $\subset \mathbb{R}$. Um conjunto A $\subset$ X é dito denso em X se $\overline{A} = X$.
\end{defn}

\begin{prop}
    Seja X $\subset \mathbb{R}$. Um subconjunto A $\subset$ X é denso em X se, e somente se, para todo a $\in$ X e para todo $\epsilon > 0$, $(a-\epsilon, a+\epsilon) \cap A \ne \varnothing.$
\end{prop}

\begin{defn}
    Um conjunto compacto em $\mathbb{R}$ é um conjunto fechado e limitado.
\end{defn}

\begin{defn}
    Chama-se cobertura de um conjunto $X \subset \mathbb{R}$ a uma família C de conjuntos $C_\lambda$ cuja reunião contém X.
\end{defn}

\begin{defn}
Seja $X \subset \mathbb{R}$. Dizemos que um conjunto X tem medida nula se para qualquer $\epsilon > 0$, existe uma cobertura finita ou infinita enumerável de X por intervalos abertos $I_k$, isto é, $X \subset \underset{\lambda\in L}{\bigcup} I_k$  tal que $\underset{\lambda\in L}{\sum} |I_k| < \epsilon$.  
\end{defn}


\subsection{Base ternária (base 3)}











































\section{A construção do conjunto de Cantor}
Consideremos o segmento que representa o intervalo fechado $\textit{I}$ = [0,1]. No primeiro passo, dividimos $\textit{I}$ em três partes iguais e, em seguida, removemos o intervalo aberto $(\frac{1}{3},\frac{2}{3})$, a qual chamaremos de terço médio de $\textit{I}$. Chamemos de C1 o conjunto dos pontos restantes de $\textit{I}$. Assim, $C_1 = [0,\frac{1}{3}]\cup[\frac{2}{3},1]$.
    \newline
No segundo passo, dividimos em três partes iguais os dois intervalos fechados de C1 e, em seguida, removemos os intervalos abertos $(\frac{1}{9}, \frac{2}{9})$ e $(\frac{7}{9},\frac{8}{9})$. Chamemos então de $C_2$ o conjunto dos pontos restantes de $C_1$. Ou seja, $C_2 = [0,\frac{1}{9}]\cup[\frac{2}{9},\frac{1}{3}]\cup[\frac{2}{3},\frac{7}{9}]\cup[\frac{8}{9},1]$.
    \newline
  Então prosseguindo indutivamente dessa maneira, de tal forma que $C_n$ é constituído dos pontos de $C_{n-1}$ retirando o terço médio aberto de $C_n$, obtemos uma sequência de conjuntos: $C_1, C_2,..., C_n,...$ tais que $\textit{I}\supset C_1 \supset C_2 \supset ... \supset C_{n-1}\supset C_n \supset$ ...
  \newline
  Observe que $C_n$ consiste em $2^{n}$ intervalos fechados e disjuntos dois a dois.

\begin{defn}
    O conjunto de Cantor $\textit{C}$ é a interseção dos conjuntos $\textit{C}_n$, obtidos através da remoção sucessiva dos terços médios abertos do intervalo $\textit{C} = [0,1]$, ou seja, $C = \bigcap\limits^\infty_{n=1}C_n$.

\end{defn}

\begin{teo}
     Os elementos do conjunto de Cantor possuem expansão ternária (base 3) usando apenas os dígitos 0 e 2, ou seja, 
     \newline
     $\textit{C} = \{x \in [0,1]: x = \sum \frac{i_n}{3^{n}}$ para $i_n = 0$ ou $i_n = 2\}$.
\end{teo}

\section{Propriedades do conjunto de Cantor}

\begin{prop}
    O conjunto $\textit{C}$ não é vazio.
\end{prop}

\textbf{Demonstração:} Pelo (Teorema), vimos que se um número pertencente a $\textit{I}$ = [0,1] cuja expansão ternária possui somente os dígitos 0 e 2, então esse número pertence ao conjunto de Cantor. Como $\frac{1}{4} = (0,0202...)_3$, então $\frac{1}{4} \in \textit{C}$. Portanto, $\textit{C} \ne \varnothing$.~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ~~~~~~~~~~~~~~~~~~~~~~~~~~$\Box$

\begin{prop}
    $\textit{C}$ é um conjunto fechado.
\end{prop}

\textbf{Demonstração:} Sejam $(T_\lambda)_{\lambda \in \mathbb{N}}$ os intervalos retirados durante a construção de $\textit{C}$. Pela (proposição), $\underset{\lambda\in \mathbb{N}}{\bigcup} T_\lambda$ é um conjunto aberto. Então, ${(\underset{\lambda\in \mathbb{N}}{\bigcup} T_\lambda)}^{C}$ é um conjunto fechado (def). Mas, $\textit{C} = {(\underset{\lambda\in \mathbb{N}}{\bigcup} T_\lambda)}^{C} \cap [0,1]$ e [0,1] é um conjunto fechado, assim pela (prop) $\textit{C}$ é um conjunto fechado.~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ $\Box$

\begin{prop}
    $\textit{C}$ é um conjunto compacto.
\end{prop}

\textbf{Demonstração:} Temos que $\textit{I}$ é um conjunto limitado e $\textit{C} \subset \textit{I}$, então $\textit{C}$ também é limitado. Pela (prop), vimos que $\textit{C}$ é fechado, e como $\textit{C}$ também é limitado, logo pela (prop) $\textit{C}$ é um conjunto compacto.~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ $\Box$

\begin{prop}
    $\textit{C}$ é um conjunto não enumerável.
\end{prop}

\begin{prop}
    O conjunto de Cantor possui interior vazio, ou seja, int($\textit{C}) = \varnothing$. 
\end{prop}

\textbf{Demonstração:} Suponha, por absurdo, que $int(\textit{C}) \ne \varnothing$ e seja x $\in int(\textit{C})$. Então, $\exists \delta$ > 0 tal que (x-$\delta$,x+$\delta) \subset \textit{C}$ pela (def).
\newline Assim, (x-$\delta$, x+$\delta) \subset C_n , \forall n \in \mathbb{N}$. Como $C_n$ é a união de $2^{n}$ intervalos disjuntos de comprimento $\frac{1}{3^{n}}$, o intervalo (x-$\delta,x+\delta$) deverá estar contido em um desses subintervalos de $C_n$. Como   $\frac{1}{3^{n}}\rightarrow 0$, então $\exists m \in \mathbb{N}$ tal que $\frac{1}{3^{n}} < \delta$. Mas, o intervalo (x-$\delta,x+\delta$) tem comprimento $2\delta > \delta>\frac{1}{3^{n}}$.
\newline Desta forma, (x-$\delta,x+\delta)$ não está contido em nenhum dos subintervalos de $C_m$, ou seja, (x-$\delta,x+\delta)\nsubseteq C_m$, o que é um absurdo. 
\newline Portanto, $int(\textit{C}) = \varnothing$.~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ $\Box$

\begin{prop}
    O conjunto $\textit{C}^C$ é denso em $[0,1]$.
\end{prop}

\begin{prop}
    O conjunto de Cantor possui medida nula.
\end{prop}










\section{Conclusão}

Art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art art art art
art art art art art art art art art art art art art.

\begin{thebibliography}{99}

\bibitem{CD} SINGH, Simon.\textit{ Fermat's Enigma: The Epic Quest to Solve the World's Greatest Mathematical}. Anchor Books, New York, 307 pp., (1997).




\end{thebibliography}


\end{document}
