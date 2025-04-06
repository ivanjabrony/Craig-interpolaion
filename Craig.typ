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

== Semantic Proof of theorem

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

== Introduction

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

Given a transition system $M=⟨I,T⟩$, BMC is an iterative process for checking $P$ in all initial paths up to a given bound on the length. 

-*Initial states (I)* - A formula describing all possible starting configurations of the system.

-*Transition relation (T)* -  A formula defining how the system moves from one state to the next.

In order to search for a counterexample of length k, the following propositional formula is built:

- $"BMC"(k) = I(s_0) and T(s_0, s_1) and T(s_1, s_2) and dots and T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

    - $italic("if satisfiable:")$ there's a counterexample
    - $italic("if unsatisfiable:")$: there's no errors that are reachable in $k$ steps
  
== Into k-step BMC

If BMC is *unsatisfiable*, then it may be spliited into two formulas^

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

*FRS* - forward reachability sequence, denoted as such $overline(F)_"[k]"$ is a sequence $⟨F_0,dots, F_k⟩$ of propositional formulas over $V$ such that the following holds:

- $F_0 = I$
- $F_i and T imply F'_"i+1" "for" 0 <= i < k$
(F' is an F but with all variables $v in V$ replaced with counterparts $v' in V'$, or starting and successor states before and after transition)

FRS are in the context of IC3 algorithm.

TODO(IC3)
TODO(FBA)
TODO(ITP)
TODO(FRS)