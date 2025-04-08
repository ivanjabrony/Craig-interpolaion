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

Given a $italic("finite")$ transition system $M=⟨V, I, T, P⟩$, BMC is an iterative process for checking $P$ in all initial paths up to a given bound on the length. 

- *V* - a set if boolean variables. V induces a set of states $S eq.def BB^"|V|"$, and a state $s in S$ is an assignment to $V$ and can be represented as a conjunction of literals that are satisfied in $s$. More generally, a formula over $V$ represents the set of states in which it is satisfiable.

Given a formula $F$ over $V$, we use $F′$ to denote the corresponding formula in which all variables v∈V have been replaced with their counterparts $v′ in V′$. In the context of multiple steps of the transition system, we use $V^i$ instead of $V′$ to denote the variables in $V$ after $i$ steps. Given a formula $F$ over $V^i$, the formula $F[V^i implied V^j]$ is identical to $F$ except that for each variable $v in V$, each occurrence of $v^i$ in $F$ is replaced with $v^j$. This substitution allows us to change the execution step to which a formula refers.

#pagebreak()

- *Initial states (I)* - A formula over $V$ describing all possible starting configurations of the system.
- *Transition relation (T)* - A formula defining how the system moves from one state to the next. $(T(V,V'))$ is a formula over the variables $V$ and their primed counterparts $V' = {v'|v in V}$, representing starting states and successor states of the transition.
- *Safe states (P)* - A formula over $V$ describing all possible safe states of the system.


== Definition 4 - Forward reachability sequence

*FRS* - forward reachability sequence, denoted as such $overline(F)_"[k]"$ is a sequence $⟨F_0,dots, F_k⟩$ of propositional formulas over $V$ such that the following holds:

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
    - $italic("if unsatisfiable:")$ there's no errors that are reachable in $k$ steps
  

=== Hard one

- $"path"^"i,j" eq.def T(V^i, V^"i+1") and dots and T(V^"j-1", V^j)$, where $0 <= i < j "and" j - i = k$. An initial path of length $k$ is defined using the formula $I(V^0) and "path"^"0,k"$.

In order to search for a counterexample of length k, the following propositional formula is built:
- $phi^k eq.def I(V^0) and "path"^"0,k" and (not P(V^k))$

#pagebreak()

If BMC is *unsatisfiable*, then it may be splitted into two formulas:

+ $A = I(s_0) and T(s_0, s_1)$
+ $T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

Since $A and B$ is *false*, then (by Craig Theorem) there's an interpolant $A'$ such as:
+ $A imply A'$
+ $A' and B$ is unsatisfiable
+ $A'$ only uses common symbols from $A$ and $B$ (e.g. state variables $s_i$)
  
== PBA, Proof-Based Abstraction

*Abstraction* is a widely-used method to mitigate the state explosion problem. Since the root of the problem is the need of model checking algorithms to exhaustively traverse the entire state space of the system, abstraction aims at reducing the state space by removing irrelevant details from the system. The irrelevant details of the system are usually determined by analyzing the checked property and finding which parts of the system are not necessary for the verification or refutation of that property.

A well-known SAT-based abstraction technique is *PBA*. One of the main advantages of SAT solvers is their ability to “zoom in” on the part that makes a CNF formula unsatisfiable. This part is referred to as the *unsatisfiable core (UC)* of the formula. If an unsatisfiable CNF formula is a set of clauses, then its UC is an unsatisfiable subset of this set of clauses. PBA uses the UC of an unsatisfiable BMC formula to derive an abstraction.

#pagebreak()

Let $phi^k$ be an unsatisfiable formula. Let's define a set

- $V_a = {v|v^i in "Vars"("UC"(phi^k)), 0 <= i <= k}$ as the set of variables from the transition system that appears in $"UC"$ of $phi^k$.

- $M_a$ - Abstract transition system derived from $M$ by making all variables $v in V "\\" V_a$ nondetermenistic.

#pagebreak()

PBA is based on the BMC loop. 

+ At each iteration, a BMC formula $phi^k$ is checked. If the formula is satisfiable, then a counterexample is found. Otherwise, a UC is extracted, and an abstract transition system $M_a$ is computed.

+ $M_a$ is passed to a complete model checking algorithm for verification. If the property is proved using the abstract model, then the algorithm terminates concluding that the property holds. Otherwise, a counterexample is found. Note that if a counterexample is found in $M_a$, it may not exist in $M$ (due to the abstraction). 

+ A counterexample that exists in $M_a$ but not in $M$ is referred to as *spurious*. In the case of a *spurious* counterexample, PBA executes the next iteration of the BMC loop with a larger $k$.


== Algorithms 

Complete SAT-based model checking algorithms are predominantly based on a search for an inductive invariant. A popular approach is *k-induction*, which aims to find a bound $k$ such that all states reachable via an initial path $I(V^0) and "path"_"0,k"$ are safe, and that whenever $P$ holds in $k$ consecutive steps of the transition system, then $P$ also holds in the subsequent step. 

The model checking algorithms discussed below search for inductive invariants by means of FRS computation and the use of Lemma 2. In case an inductive invariant that implies $P$ is found, $M$ is reported to be safe.


== ITP, Interpolation-Based Model Checking

*ITP* is a complete SAT-based model checking algorithm that relies on interpolation to compute the FRS and uses interpolation to synthesize an inductive invariant during the exploration. 


=== Revisiting BMC

As we know, BMC formulates the question: “Does $M$ have a counterexample of length $k$?” as a propositional formula $phi^k$. In a similar manner, BMC can also be formulated using the question “Does $M$ have a counterexample of length $i$ such that $1 ≤ i ≤ k$?” by using the following propositional formula:

- $psi^k eq.def I(V^0) and "path"^"0, k" and (or.big^k_"i=1" not P(V^i))$

ITP uses nested loops where the inner loop computes a $italic("safe")$ FRS by repeatedly checking formulas of the form $psi^k$ with a fixed $k$, and the outer loop increases the bound k when needed. The safe FRS is computed inside the inner loop by extracting interpolants from unsatisfiable BMC formulas.


== Inner loop of ITP

In general, the inner loop checks a fixed-bound BMC formula. At the first iteration, $psi^k$ is checked. If this BMC formula is satisfiable, then a counterexample exists and the algorithm terminates. If it is unsatisfiable, then the following expressions defined:

- $A eq.def I(V^0) and T(V^0, V^1)$
- $B eq.def "path"^"1, k" and (or.big^k_"i=1" not P(V^i))$
  
By Definition 1 and interpolant $I_1^k$ is extracted. To make sure it's an interpolant indeed:

+ It represents an overapproximation of the states from $I$ after one transition ($A imply I_1^k$)
+ No counterexample can be reached from $I_1^k "in" k-1$ transitions or less ($I_1^k and B$ is unsatisfiable), which also guarantees that $I_1^k imply P$.

This, the sequence $⟨I, I^k_1 [V^1 implied V]⟩$ is a valid FRS.

In the subsequent iterations, the formula $psi^k [I implied I^k_"j−1"]$ is checked, where $j$ is the iteration of the inner loop. Thus, in the $j$th iteration, if $psi^k [I implied I^k_"j−1"]$ is unsatisfiable, an interpolant $I^k_j$ is extracted with respect to the $(A, B)$ pair where $A = I^k_"j−1" (V^1 implied V^0) and T(V^0, V^1)$ and $B$ is as before. Following this definition, $I^k_j$ is an overapproximation of states reachable from $I_k^"j−1"$ in one transition and $⟨I, I^k_1, dots , I^k_j⟩$ is a safe FRS.

The inner loop terminates either when the BMC formula it checks is satisfiable, or when an inductive invariant is found. In the latter case, the algorithm terminates concluding that the transition system is safe. In the former case, there are two cases to handle: If the BMC formula is satisfiable in the first iteration, a counterexample exists and the algorithm terminates, otherwise, the control is passed back to the outer loop, which increases $k$.

== Outer loop of ITP

After the first iteration of the inner loop, overapproximated sets of reachable states are used as the initial condition of the checked BMC formulas. 
Even if formula is satisfiable, it is not clear if it is due to the existence of a counterexample or due to the overapproximation. 
To make calculation more precise, puter loop increases the bound $k$ used for the BMC queries. Increasing k helps to either find a real counterexample or to increase the precision of the overapproximation.


== Interpolation Sequence-Based Model Checking

ISB was suggested for a computation of a safe FRS as a part of the main BMC loop. Unlike ITP, ISB has no nested loops and integrated into BMC's main loop.

It's pretty much the same with ITP in concept so there's a shortened version of how algorithm works.

- Starting point is $⟨F_0 = I⟩$ as an FRS. At first operation it solves $phi^1$.
- At $k$th iteration, the FRS is $⟨F_0, dots, F_"k-1"⟩$ and $phi^k$ is checked. The goal of this step is to extend FRS with new element $F_k$. If $phi^k$ is satisfiable, a counterexample is found and the algorithm terminates
- If it is not, an interpolation sequence $⟨I_0^k, dots, I_k^k⟩$ is extracted and used to extend current FRS. The $i$th element of existing FRS is updated by defining:
  - $F_i = F_i and I^k_i [V^i implied V] "for" i <= i < k$ and $F_k$ to be $I_k^k (F_k = I_k^k[V^k implied V])$.
- The result is a safe FRS of length $k$. If at the end of $k$th iteration an inductive invariant is found (Lemma 2), the algorithm terminates concluding that M is safe.

== IC3
TODO(IC3)
