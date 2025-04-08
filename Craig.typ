#import "theme.typ": *
#show: slides.with(
  title: [Formal Methods in Software Engineering],
  subtitle: "Propositional Logic",
  date: "Spring 2025",
  authors: "Konstantin Chukharev",
  ratio: 16 / 9,
  // dark: true,
)

// custom style
#show heading.where(level: 3): set block(above: 1em, below: 0.6em)
#show table.cell.where(y: 0): strong

// proof trees
#import curryst: rule, prooftree

// semantical evaluation
#let Eval(x) = $bracket.l.double #x bracket.r.double_nu$

// smash
#let smash(it) = box(width: 0pt, align(center, box(width: float.inf * 1pt, it)))

= Craig Interpolation in Module checking

== Introduction into Craig Interpolation Theorem

*Craig interpolation theorem* states:
  If there's such a formulas $A$ and $B$ and $A models B$ then exists such formula $C$ that:
- $A models C$ 
- $C models B$
- $C$ only consists of non-logical $A and B$

*Real-world examples*:
- K-step BMC.
- TODO.
- TODO.

== Semantic Proof of theorem

Let $L_a$ be a language of $A$ and $L_b$ a language of $B$.

$L_"AB" = L_A and L_B$

=== Example
Let $A = P(X) and Q(X)$, $B = Q(Y) or R(Y)$, then
- $L_A = {P, Q}$
- $L_B = {Q, R}$
- $L_"AB" = {Q}$

=== Step 1
$G = {phi in L_"AB" | A models phi}.$

$G$ - a set of formulas that are true if $A$ is true.

#pagebreak()

=== Step 2
We neeed to show, that if some model $M$ satisfies all formulas from $G$, then it implies B automatically.

Let $M$ be a model of $G$. ($forall gamma in G :M models gamma$)

We are expanding $M$ up to a $M'$ by adding interpretation of symbols from $L_A\\L_"AB"$ so $M' models A$

It is possible because $G$ already contains all consequences of $A$ in $L_"AB"$


=== Step 3
If $A models B$, then $M' models B$
because $B$ depends only on symbols from $L_B$ and $M'$ equals with $M$ on $L_"AB" in L_B$, then $M models B$

In result, *any model* of $G$ satisfies $B$, means $G models B$

By Theorem of compactness, if $G models B$, then exists a finite set of $phi_1, phi_2,dots, phi_n$ from $G$ such as that $(phi_1 and phi_2 and dots phi_n) models B$

Then our *interpolant* is $C = phi_1 and phi_2 and dots phi_n$ 

#pagebreak()

=== Checking of C
+ $A models B$ because every formula in $G$ is a consequence of $A$
+ $C models B$ from proof
+ $C$ only uses symbols from $L_"AB"$

*Example*: $A = P(x) and Q(x), B = Q(y) or R(y)$

$C - ?$



= SAT and usage Module checking

== Definition 1 - Interpolant

- Let $A$ and $B$ be quantifier-free propositional formulas whose conjunction $A and B$ is unsatisfiable. An interpolant is a quantifier-free propositional formula $I$ such that $A imply I$ is valid, $I and B$ is unsatisfiable, and the variables occurring in $I$ are a subset of the variables common to $A$ and $B$.

Intuitively, if $A$ represents reachable states and $B$ unsafe or bad states, then the interpolant $I$ safely overapproximates $A$, a property frequently used in the context of fixed-point detection. (More about it later)

== Definition 2 - Interpolant sequence

Let $⟨A_1, A_2, dots, A_n⟩$ be an ordered sequence of propositional formulas such that the conjunction $and.big^n_"i=1" A_i$ is unsatisfiable. An interpolation sequence is a sequence of formulas $⟨I_0, I_1, dots, I_n⟩$ such that all of the following conditions hold.

+ $I_0=T$ and $I_n=F$.

+ For every $0 ≤ j < n$, $I_j and A_"j+1" imply I_"j+1"$ is valid.

+ For every $0 < j < n$, it holds that the variables in $I_j$ are a subset of the common variables of $⟨A_1, dots, A_j⟩$ and $⟨A_"j+1", dots , A_n⟩$.


== Definiton 3 - Finite-state Transition System

iven a $italic("finite")$ transition system $M=⟨V, I, T, P⟩$, BMC is an iterative process for checking $P$ in all initial paths up to a given bound on the length. 

-*V* - a set if boolean variables. V induces a set of states $S eq.def BB^"|V|"$, and a state $s in S$ is an assignment to $V$ and can be represented as a conjunction of literals that are satisfied in $s$. More generally, a formula over $V$ represents the set of states in which it is satisfiable.

Given a formula $F$ over $V$, we use $F′$ to denote the corresponding formula in which all variables v∈V have been replaced with their counterparts $v′ in V′$. In the context of multiple steps of the transition system, we use Vi instead of $V′$ to denote the variables in $V$ after $i$ steps. Given a formula $F$ over $V^i$, the formula $F[V^i implied V^j]$ is identical to F except that for each variable $v in V$, each occurrence of $v^i$ in $F$ is replaced with $v^j$. This substitution allows us to change the execution step to which a formula refers.

#pagebreak()

-*Initial states (I)* - A formula over $V$ describing all possible starting configurations of the system.

-*Transition relation (T)* - A formula defining how the system moves from one state to the next. $(T(V,V'))$ is a formula over the variables $V$ and their primed counterparts $V' = {v'|v in V}$, representing starting states and successor states of the transition.

-*Safe states (P)* - A formula over $V$ describing all possible safe states of the system.


== Definition 4 - Forward reachability sequence

- *FRS* - forward reachability sequence, denoted as such $overline(F)_"[k]"$ is a sequence $⟨F_0,dots, F_k⟩$ of propositional formulas over $V$ such that the following holds:

- $F_0 = I$
- $F_i and T imply F'_"i+1" "for" 0 <= i < k$
- A reachability sequence $overline(F)_"[k]"$ is monotonic if $F_i imply F_"i+1" "for" 0 <= i < k$ and safe if $F_i imply P "for" 0 <= i <= k$.
- The individual propositional formulas $F_i$ are called elements or frames of the sequence.

An element $F_i$ in an FRS $overline(F)_"[k]"$ represents an overapproximation of states reachable in $i$ steps of the transition system. If the FRS $italic("is monotonic")$, then $F_i$ is an overapproximation of all states reachable in at most $i$ steps. 

- *Fixpoint* -  $overline(F)$ is a fixpoint, if there is $0 < i <= k$ and $F_i imply or.big_"i=0"^"k-1"F_i$

Monotonic FRS arise in the context of IC3 algorithm.

== Definition 5 - Inductive invariant, Consecution

A set of states characterized by the formula $F$ is inductive (satisfies consecution, respectively) if $F and T imply F′$ holds. $F$ is inductive relative to a formula $G$ if $G and F and T imply F′$ holds. $F$ satisfies initiation if $I imply F$, i.e., if $F$ comprises all initial states. $F$ is safe with respect to $P$ if $F imply P$.

We say that $F$ is an inductive invariant if it satisfies initiation and is inductive.

=== Lemma 1

Let $M = ⟨V, I, T, P⟩$ be a transition system and let $F$ be a propositional formula representing a set of states. If $F$ is an inductive invariant that implies $P$ (i.e., $F imply P$ is valid), then $P$ holds in $M$ and $M$ is said to be safe.

The following lemma highlights the relationship between inductive invariants and FRS.

=== Lemma 2

Let $M$ be a transition system $⟨V, I, T, P⟩$ and let $overline(F)_"[k]"$ be an FRS. Let us define $F eq.def or.big^i_"j=0" F_j$ where $0 ≤ i < k$. Then, $F$ is an inductive invariant if $F_"i+1" imply P$. In addition, if $overline(F)_"[k]"$ is safe, then $F imply P$ holds, and thus $M$ is safe. 


== Model checking algorithms

*SAT-solver* - checks satisfiability of a certain boolean formula.

*Module checking* - verification if model of a system is correct.

Module checking and SAT are connected by methods of *Symbolic verification and symbolic model checking*.

*Symbolic model checking* - an important hardware model checking technique. In symbolic model checking, sets of states and transition relations of circuits are represented as formulas of explicit sates.

Current design blocks with well-defined functionality have many thousands of state elements. To handle such a scale, researchers deployed SAT solvers, starting with the invention of SAT-based BMC.

Bounded model checking (BMC) relies on SAT solvers to exhaustively check hardware designs up to a limited depth.

== BMC, Bounded model checking

A SAT solver either finds a satisfying assignment for a propositional formula or proves its absence. Using this terminology, BMC determines whether a transition system has a counterexample of a given length $k$ or proves its absence. 

BMC uses a SAT solver to achieve this goal. Given a transition system $M$, BMC translates the question “Does $M$ have a counterexample of length $k$?” into a propositional formula and uses a SAT solver to determine if the formula is satisfiable or not. 

If the solver finds a satisfying assignment, a counterexample exists and is represented by the assignment. If the SAT solver proves that no satisfying assignment exists, then BMC concludes that no counterexample of length $k$ exists.

#pagebreak()

In order to search for a counterexample of length k, the following propositional formula is built:

=== Easy formula
- $"BMC"(k) = I(s_0) and T(s_0, s_1) and T(s_1, s_2) and dots and T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

    - $italic("if satisfiable:")$ there's a counterexample
    - $italic("if unsatisfiable:")$: there's no errors that are reachable in $k$ steps
  

=== Hard one

- $"path"^"i,j" eq.def T(V^i, V^"i+1") and dots and T(V^"j-1", V^j)$, where $0 <= i < j "and" j - i = k$. An initial path of length $k$ is defined using the formula $I(V^0) and "path"^"0,k"$.

In order to search for a counterexample of length k, the following propositional formula is built:
- $phi^k eq.def I(V^0) and "path"^"0,k" and (not P(V^k))$

== Into k-step BMC

If BMC is *unsatisfiable*, then it may be splitted into two formulas:

+ $A = I(s_0) and T(s_0, s_1)$
+ $T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

Since $A and B$ is *false*, then (by Craig Theorem) there's an interpolant $A'$ such as:
+ $A imply A'$
+ $A' and B$ is unsatisfiable
+ $A'$ only uses common symbols from $A$ and $B$ (e.g. state variables $s_i$)

#pagebreak()

=== Interpolant

Extracted interpolant represents an overapproximation of reachable states from $I$ after one transition. In addition, no counterexample can be reached from $I$ in $k-1$ transitions or less.

When $k$ is increased, the precision of the computated interpolant is also increased. For a sufficiently large k, the approximation obtained through interpolation becomes precise enough such that algorithm is guaranteed to find an inductive invariant if the system is safe.

== ITP, Interpolation-Based Model Checking

*ITP* is a complete SAT-based model checking algorithm that relies on interpolation to compute the FRS. 

To make it short, ITP replaces accurate calculation of FRS with interpolants' approximation, which makes algorithm faster.

There's a Lemma that states: A FRS of length n exists iff there is no counterexample of length <= n. 


TODO(IC3)
TODO(FBA)
TODO(ITP)
TODO(FRS)