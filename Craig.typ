#import "theme.typ": *
#show: slides.with(
  title: [Craig Interpolation in Model Checking],
  subtitle: "Propositional Logic",
  date: "Spring 2025",
  authors: "Zabrodin Ivan",
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



= Craig Interpolation in Model checking

== Introduction into Craig Interpolation Theorem

#theorem("Craig interpolation theorem")[
  If there's such a formulas $A$ and $B$ and $A models B$ then exists such formula $C$ that:
- $A models C$ 
- $C models B$
- $C$ only consists of non-logical $A and B$]

*Real-world examples*:
- K-step BMC.
- ISB.
- IC3.

== Semantic Proof of theorem

=== Step 1

Let $L_A$ be a language of $A$ and $L_B$ a language of $B$.

$L_"AB" = L_A and L_B$

#example[
Let $A = P(X) and Q(X)$, $B = Q(Y) or R(Y)$, then
- $L_A = {P, Q}$
- $L_B = {Q, R}$
- $L_"AB" = {Q}$
]

$G = {phi in L_"AB" | A models phi}.$
$G$ - a set of formulas that are true if $A$ is true.

#pagebreak()

=== Step 2
We neeed to show, that if some model $M$ satisfies all formulas from $G$, then it implies B automatically.

Let $M$ be a model of $G$. ($forall gamma in G :M models gamma$)

We are expanding $M$ up to a $M'$ by adding interpretation of symbols from $L_A\\L_"AB"$ so $M' models A$

It is possible because $G$ already contains all consequences of $A$ in $L_"AB"$

#pagebreak()

=== Step 3
If $A models B$, then $M' models B$.

Because $B$ depends only on symbols from $L_B$ and $M'$ equals with $M$ on $L_"AB" in L_B$, then $M models B$

In result, *any model* of $G$ satisfies $B$, means $G models B$

By Theorem of compactness, if $G models B$, then exists a finite set of $phi_1, phi_2,dots, phi_n$ from $G$ such as that $(phi_1 and phi_2 and dots phi_n) models B$

Then our *interpolant* is $C = phi_1 and phi_2 and dots phi_n$ 

#pagebreak()

=== Checking of C
+ $A models C$ because every formula in $G$ is a consequence of $A$
+ $C models B$ from proof
+ $C$ only uses symbols from $L_"AB"$

*Example*: $A = P(x) and Q(x), B = Q(y) or R(y)$

$C - ?$

#pagebreak()

#{ ```py
def craig_interpolate(A, B):
    """
    A, B: Input formulas where A ∧ B is unsatisfiable
    Returns: Interpolant I satisfying:
        1. A → I
        2. I ∧ B is unsat
        3. vars(I) ⊆ vars(A) ∩ vars(B)
    """
    if sat_solver(A ∧ B) == SAT:
        raise Exception("A ∧ B must be unsatisfiable")
    proof = get_proof(A ∧ B)
    I = extract_interpolant(proof)
    
    assert implies(A, I), "A does not imply I"
    assert unsat(I ∧ B), "I ∧ B is satisfiable"
    assert (vars(I) <= vars(A) & vars(B)), "I has extra variables"
    
  return I
 ``` }

= SAT and usage Model checking

== Definition 1 - Interpolant

#definition[Let $A$ and $B$ be quantifier-free propositional formulas whose conjunction $A and B$ is unsatisfiable. An *interpolant* is a quantifier-free propositional formula $I$ such that: 
- $A imply I$ is valid 
  
- $I and B$ is unsatisfiable
  
- The variables occurring in $I$ are a subset of the variables common to $A$ and $B$.]

Intuitively, if $A$ represents reachable states and $B$ unsafe or bad states, then the interpolant $I$ safely overapproximates $A$, a property frequently used in the context of fixed-point detection. (More about it later)

== Definition 2 - Interpolation sequence

#definition[Let $⟨A_1, A_2, dots, A_n⟩$ be an ordered sequence of propositional formulas such that the conjunction $and.big^n_"i=1" A_i$ is unsatisfiable. An interpolation sequence is a sequence of formulas $⟨I_0, I_1, dots, I_n⟩$ such that all of the following conditions hold.

+ $I_0=TT$ and $I_n=FF$.

+ For every $0 ≤ j < n$,  $I_j and A_"j+1" imply I_"j+1"$ is valid.

+ For every $0 < j < n$,  it holds that the variables in $I_j$ are a subset of the common variables of $⟨A_1, dots, A_j⟩$ and $⟨A_"j+1", dots , A_n⟩$.
]

== Definiton 3 - Finite-state Transition System

#definition[Given a $italic("finite")$ transition system $M=⟨V, I, T, P⟩$:

- *V* - a set of boolean variables. $V$ induces a set of states $S eq.def BB^"|V|"$, and a state $s in S$ is an assignment to $V$ and can be represented as a conjunction of literals that are satisfied in $s$. More generally, a formula over $V$ represents the set of states in which it is satisfiable.
]
Given a formula $F$ over $V$, we use $F′$ to denote the corresponding formula in which all variables $v in V$ have been replaced with their counterparts $v′ in V′$. In the context of multiple steps of the transition system, we use $V^i$ instead of $V′$ to denote the variables in $V$ after $i$ steps. Given a formula $F$ over $V^i$, the formula $F[V^i implied V^j]$ is identical to $F$ except that for each variable $v in V$, each occurrence of $v^i$ in $F$ is replaced with $v^j$. This substitution allows us to change the execution step to which a formula refers.

#pagebreak()

- *Initial states (I)* - A formula over $V$ describing all possible starting configurations of the system.

- *Transition relation (T)* - A formula defining how the system moves from one state to the next. $(T(V,V'))$ is a formula over the variables $V$ and their primed counterparts $V' = {v'|v in V}$, representing starting states and successor states of the transition.

- *Safe states (P)* - A formula over $V$ describing all possible safe states of the system (an invariant or a condition that must always hold).


#example("Simple transition system")[
  - $V = {x, y}$
  - $I = (x = 0 and y = 0)$
  - $T = (x' = x + 1 and y' = y + x)$
  - $P = (y >= 0)$
]

== Definition 4 - Forward reachability sequence

#definition[
*FRS* - forward reachability sequence, denoted as such $overline(F)_"[k]"$ is a sequence $⟨F_0,dots, F_k⟩$ of propositional formulas over $V$ such that the following holds:

- $F_0 = I$
- $F_i and T imply F'_"i+1" "for" 0 <= i < k$
- A reachability sequence $overline(F)_"[k]"$ is monotonic if #box[$F_i imply F_"i+1" "for" 0 <= i < k$] and safe if #box[$F_i imply P "for" 0 <= i <= k$].
- The individual propositional formulas $F_i$ are called elements or frames of the sequence.

An element $F_i$ in an FRS $overline(F)_"[k]"$ represents an overapproximation of states reachable in $i$ steps of the transition system. If the FRS $italic("is monotonic")$, then $F_i$ is an overapproximation of all states reachable in at most $i$ steps. 

- *Fixpoint* -  $overline(F)$ is a fixpoint, if there is $0 < i <= k$ and $F_i imply or.big_"i=0"^"k-1"F_i$

Monotonic FRS arise in the context of IC3 algorithm.
]
== Definition 5 - Inductive invariant, Consecution

#definition[
- A set of states characterized by the formula $F$ is inductive (satisfies consecution, respectively) #box[if $F and T imply F′$ holds] 

- $F$ is inductive relative to a formula $G$ if $G and F and T imply F′$ holds 
  
- $F$ satisfies initiation if $I imply F$, i.e., if $F$ comprises all initial states 

- $F$ is safe with respect to $P$ if $F imply P$

We say that $F$ is an inductive invariant if it satisfies initiation and is inductive.
]

#pagebreak()

#example("Initiation")[
  Let $I = (x = 0)$ (system starts with $x = 0$).

  If $F = (x >= 0)$, then $I imply F$ holds because $x = 0$ implies $x >= 0$.
  
  But if $F = (x > 0)$, initiation fails because $x = 0$ does not satifsy $x > 0$.
] 


#example("Inductivness/Consecution")[
  Let $F = (x >= 0)$ and $T = (x' = x + 1)$.
  
  Check: $(x >= 0) and (x' = x + 1) imply (x' >= 0)?$ 
  - Yes, because if $x >= 0$ then $x' = x + 1 >= 0$.
  
  Thus, $F$ is inductive.
] 

#example("Inductive Relative")[
  Let $F = (x <= 10)$, $T = (x' = x + 1)$ and $G = (x <= 9)$.
  
  Check: $(x <= 9) and (x <= 10) and (x' = x + 1) imply (x' <= 10)?$
  - Yes, because if $x <= 9$ then $x' = x + 1 <= 10$.
  
  Here, $F$ is inductive relative to $G$, but not fully inductive.
]

#pagebreak()

#example("Safety")[
  Let $F = (x <= 5)$, $P = (x <= 10)$.
  
  Then $F imply P$ holds because $x <= 5$ implies $x <= 10$.
  
  But if $F = (x <= 15)$, then $F imply P$ fails.
]


#example("Inductive Invariant")[
  Let $I = (x = 0)$, $T = (x' = x + 1)$ and $P = (x >= 0)$.
  
  Let $F = (x <= 10)$.
  - *Initiation:* $I imply F$ holds $(x = 0 >= 0)$.
  - *Consecution:* $(x >= 0) and (x' = x + 1) imply (x' >= 0)$ holds.
  
  Thus, $F$ is inductive invariant.
]

== Lemmas

=== Lemma 1

Let $M = ⟨V, I, T, P⟩$ be a transition system and let $F$ be a propositional formula representing a set of states. 
If $F$ is an inductive invariant that implies $P$ (i.e., $F imply P$ is valid), then $P$ holds in $M$ and $M$ is said to be safe.

The following lemma highlights the relationship between inductive invariants and FRS.

=== Lemma 2

Let $M$ be a transition system $⟨V, I, T, P⟩$ and let $overline(F)_"[k]"$ be an FRS. 
Let us define #box[$F eq.def or.big^i_"j=0" F_j$ where $0 ≤ i < k$.] 

Then, $F$ is an inductive invariant if $F_"i+1" imply F$. In addition, if $overline(F)_"[k]"$ is safe, then $F imply P$ holds, and thus $M$ is safe. 


== Model checking algorithms

*SAT-solver* - checks satisfiability of a certain boolean formula.

*Model checking* - verification if model of a system is correct.

Model checking and SAT are connected by methods of *Symbolic verification and symbolic model checking*.

*Symbolic model checking* - an important hardware model checking technique. In symbolic model checking, sets of states and transition relations of circuits are represented as formulas of explicit states.

Current design blocks with well-defined functionality have many thousands of state elements. To handle such a scale, researchers deployed SAT solvers, starting with the invention of SAT-based BMC.

Bounded model checking (BMC) relies on SAT solvers to exhaustively check hardware designs up to a limited depth.

== BMC, Bounded model checking

A SAT solver either finds a satisfying assignment for a propositional formula or proves its absence. Using this terminology, BMC determines whether a transition system has a counterexample of a given length $k$ or proves its absence. 

BMC uses a SAT solver to achieve this goal. Given a transition system $M$, BMC translates the question “Does $M$ have a counterexample of length $k$?” into a propositional formula and uses a SAT solver to determine if the formula is satisfiable or not. 

If the solver finds a satisfying assignment, a counterexample exists and is represented by the assignment. If the SAT solver proves that no satisfying assignment exists, then BMC concludes that no counterexample of length $k$ exists.

#pagebreak()

*Representation of how algorithm works*
#image("/static/bmc.png")

BMC checks whether a property $P$ can be violated in $k$ steps by encoding reachable sets of states $(R_1, dots, R_k)$ as a SAT instance. BMC does not identify repeatedly visited states and can therefore not determine whether the property holds for arbitrarily many steps.

#pagebreak()

In order to search for a counterexample of length k, the following propositional formulas are built:

=== Easy formula
- $"BMC"(k) = I(s_0) and T(s_0, s_1) and T(s_1, s_2) and dots and T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

    - $italic("if satisfiable:")$ there's a counterexample
    - $italic("if unsatisfiable:")$ there's no errors that are reachable in $k$ steps
  

=== Hard one

Let $"path"^"i,j" eq.def T(V^i, V^"i+1") and dots and T(V^"j-1", V^j)$, where $0 <= i < j "and" j - i = k$. 

An initial path of length $k$ is defined using the formula $I(V^0) and "path"^"0,k"$,
then:
- $phi^k eq.def I(V^0) and "path"^"0,k" and (not P(V^k))$

#pagebreak()

If BMC is *unsatisfiable*, then it may be splitted into two formulas:

+ $A = I(s_0) and T(s_0, s_1)$
+ $T(s_1, s_2) and dots and T(s_"k-1", s_k) and (psi(s_0) or psi(s_1) or dots or psi(s_k))$

If $A and B$ is *unsatisfiable* by SAT, then (by Craig Theorem) there's an interpolant $A'$ such as:
+ $A imply A'$
+ $A' and B$ is unsatisfiable
+ $A'$ only uses common symbols from $A$ and $B$ (e.g. state variables $s_i$)

This interpolant $A'$ overapproximates reachable states in $k$ transitions.

#pagebreak()


 #{```py 
 def bounded_model_checking(M, P, max_depth):
    """
    M: Transition system (V, I, T)
    P: Safety property to verify
    max_depth: Maximum unrolling depth to check
    Returns: Verification result and counterexample if found
    """
    for k in range(0, max_depth + 1):
        # I ∧ T₀ ∧ T₁ ∧ ... ∧ T_{k-1} ∧ ¬P_k
        formula = []
        
        formula.append(M.I)  # I at time 0
        
        for i in range(k):
            # Instantiate T at each time step
            Ti = substitute(M.T, {'current': i, 'next': i+1})
            formula.append(Ti)
```}
#pagebreak()
#{```py        
        notPk = substitute(¬P, {'current': k})
        formula.append(notPk)
        
        cnf = convert_to_cnf(conjunction(formula))
        result = sat_solver(cnf)
        
        if result == SAT:
            trace = []
            for t in range(k+1):
                state = {}
                for var in M.V:
                    state[var] = get_assignment(var, t)
                trace.append(state)
            return ("Violation found at depth", k, trace)
    return ("Property holds up to depth", max_depth)
# Example Usage:
# M = TransitionSystem(V={'x'}, I='x==0', T='x_next == x + 1')
# result = bounded_model_checking(M, P='x <= 3', max_depth=5)
 ```}

== PBA, Proof-Based Abstraction

*Abstraction* is a widely-used method to mitigate the state explosion problem. Since the root of the problem is the need of model checking algorithms to exhaustively traverse the entire state space of the system, abstraction aims at reducing the state space by removing irrelevant details from the system. The irrelevant details of the system are usually determined by analyzing the checked property and finding which parts of the system are not necessary for the verification or refutation of that property.

A well-known SAT-based abstraction technique is *PBA*. One of the main advantages of SAT solvers is their ability to “zoom in” on the part that makes a CNF formula unsatisfiable. This part is referred to as the *unsatisfiable core (UC)* of the formula. If an unsatisfiable CNF formula is a set of clauses, then its UC is an unsatisfiable subset of this set of clauses. PBA uses the UC of an unsatisfiable BMC formula to derive an abstraction.

#pagebreak()

Let $phi^k$ be an unsatisfiable formula. Let's define a set

- $V_a = {v|v^i in "Vars"("UC"(phi^k)), 0 <= i <= k}$ as the set of variables from the transition system that appears in $"UC"$ of $phi^k$.

- $M_a$ - Abstract transition system derived from $M$ by making all variables $v in V "\\" V_a$ nondetermenistic.

*Nondetermenistic* means that the states of the variables *not from $V_a$* are not determined and they may have any value. Other variables in $V_a$ are still bounded by the rules of model $M$.

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

*Representation of how algorithm works*
#image("static/itp.png", width: 60%)

Interpolation-based model checking partitions an unsatisfiable BMC instance into a formula $A$ representing initial states and the first step, and a formula $B$ representing the states from which a property $P$ can be violated within $k−1$ steps. The interpolant $I^k_1$ safely overapproximates all states reachable in a single step and is used to extend the FRS.

#pagebreak()

=== Revisiting BMC

As we know, BMC formulates the question: #box[“Does $M$ have a counterexample of length $k$?”] as a propositional formula $phi^k$. In a similar manner, BMC can also be formulated using the question #box[“Does $M$ have a counterexample of length $i$ such that $1 ≤ i ≤ k$?”] by using the following propositional formula:

- $psi^k eq.def I(V^0) and "path"^"0, k" and (or.big^k_"i=1" not P(V^i))$

ITP uses nested loops where the inner loop computes a $italic("safe")$ FRS by repeatedly checking formulas of the form $psi^k$ with a fixed $k$, and the outer loop increases the bound k when needed. The safe FRS is computed inside the inner loop by extracting interpolants from unsatisfiable BMC formulas.


== Inner loop of ITP

In general, the inner loop checks a fixed-bound BMC formula. At the first iteration, $psi^k$ is checked. If this BMC formula is satisfiable, then a counterexample exists and the algorithm terminates. If it is unsatisfiable, then the following expressions defined:

- $A eq.def I(V^0) and T(V^0, V^1)$
- $B eq.def "path"^"1, k" and (or.big^k_"i=1" not P(V^i))$
  
By Definition 1 an interpolant $I_1^k$ is extracted. To make sure it's an interpolant indeed:

+ It represents an overapproximation of the states from $I$ after one transition ($A imply I_1^k$)
+ No counterexample can be reached from $I_1^k "in" k-1$ transitions or less ($I_1^k and B$ is unsatisfiable), which also guarantees that $I_1^k imply P$.

#pagebreak()

Thus, the sequence $⟨I, I^k_1 [V^1 implied V]⟩$ is a valid FRS.

In the subsequent iterations, the formula $psi^k [I implied I^k_"j−1"]$ is checked, where $j$ is the iteration of the inner loop. Thus, in the $j$th iteration, if $psi^k [I implied I^k_"j−1"]$ is unsatisfiable, an interpolant $I^k_j$ is extracted with respect to the $(A, B)$ pair where $A = I^k_"j−1" (V^1 implied V^0) and T(V^0, V^1)$ and $B$ is as before. Following this definition, $I^k_j$ is an overapproximation of states reachable from $I_k^"j−1"$ in one transition and $⟨I, I^k_1, dots , I^k_j⟩$ is a safe FRS.

The inner loop terminates either when the BMC formula it checks is satisfiable, or when an inductive invariant is found. In the latter case, the algorithm terminates concluding that the transition system is safe. In the former case, there are two cases to handle: If the BMC formula is satisfiable in the first iteration, a counterexample exists and the algorithm terminates, otherwise, the control is passed back to the outer loop, which increases $k$.

== Outer loop of ITP

After the first iteration of the inner loop, overapproximated sets of reachable states are used as the initial condition of the checked BMC formulas. 
Even if formula is satisfiable, it is not clear if it is due to the existence of a counterexample or due to the overapproximation. 
To make calculation more precise, outer loop increases the bound $k$ used for the BMC queries. Increasing k helps to either find a real counterexample or to increase the precision of the overapproximation.

Note that $B$ represents all bad states and all states that can reach a bad state in $k−1$ transitions or less. Therefore, when $k$ is increased, the precision of the computed interpolant is also increased. For a sufficiently large $k$, the approximation obtained through interpolation becomes precise enough such that the inner loop is guaranteed to find an inductive invariant if the system is safe, leading to the termination of the algorithm.


== Interpolation Sequence-Based Model Checking

ISB was suggested for a computation of a safe FRS as a part of the main BMC loop. Unlike ITP, ISB has no nested loops and integrated into BMC's main loop.

*Representation of how algorithm works*
#image("static/isb.png", width: 75%)
Interpolation sequence-based model checking partitions an unsatisfiable BMC instance into $k+1$ partitions (with the last one representing the “bad” states), resulting in the interpolants $I^k_1, dots, I^k_k$. Each $I^k_i$ overapproximates the states reachable in $i$ steps, and states in $I^k_"i+1" $are reachable from $I^k_i$ in a single step.

#pagebreak()

It's pretty much the same with ITP in concept so there's a shortened version of how algorithm works.

- Starting point is $⟨F_0 = I⟩$ as an FRS. At first operation it solves $phi^1$.
- At $k$th iteration, the FRS is $⟨F_0, dots, F_"k-1"⟩$ and $phi^k$ is checked. The goal of this step is to extend FRS with new element $F_k$. If $phi^k$ is satisfiable, a counterexample is found and the algorithm terminates
- If it is not, an interpolation sequence $⟨I_0^k, dots, I_k^k⟩$ is extracted and used to extend current FRS. The $i$th element of existing FRS is updated by defining:
  - $F_i = F_i and I^k_i [V^i implied V] "for" i <= i < k$ and $F_k$ to be $I_k^k (F_k = I_k^k [V^k implied V])$.
- The result is a safe FRS of length $k$. If at the end of $k$th iteration an inductive invariant is found #box[(Lemma 2)], the algorithm terminates concluding that M is safe.

== IC3
*IC3* (Incremental Construction of Inductive Clauses) is a SAT-based algorithm that incrementally refines inductive invariants to prove safety properties. It operates on a Forward Reachability Sequence (FRS), blocking counterexamples via interpolation, and can integrate abstractions (e.g., FBA) for efficiency. Unlike BMC, IC3 avoids full unrolling, making it scalable for large systems.

Unlike interpolation-based techniques, IC3 does not depend on the unpredictable result of an interpolation engine.

#pagebreak()

#image("static/ic3.png", width: 60%)

IC3 maintains a monotonic sequence of frames $F_1, dots ,F_k$ that overapproximate the states reachable in up to $k$ steps. The approximation is iteratively refined by eliminating from frame $F_i$ states $t$ that are predecessors of a state in $not P$, but have themselves no predecessor in $F_"i−1"$ (i.e., $not t$ is inductive relative to $F_"i−1"$ and #box[$F_"i−1" and not t and T imply not t′$] holds).


#pagebreak()

IC3's search strategy is based on a backward search that starts from the unsafe (or “bad”) states in $not P$. The algorithm maintains a *monotonic safe* FRS $F_0, dots, F_k$, where each frame $F_i$ overapproximates the set of states reachable from $I$ in up to $i$ steps of $T$. In addition, IC3 maintains a queue of states $s$ occurring in the FRS from which a bad state is reachable (via a sequence of steps from $s$ to a state in $not P$, which we call a bad suffix). 

At each iteration, IC3 picks a state $s$ from the queue, prioritizing states in frames with lower indices. Assume that $s$ occurs in $F_k$. Then, IC3 tries to find a one-step predecessor to $s$ in $F_"k−1"$ in an attempt to extend the bad suffix until an initial state is reached. If the bad suffix is found to be unreachable (i.e., no predecessor $t$ exists), then IC3 blocks the suffix using a process called inductive generalization.

The generalization technique yields a clause that is inductive relative to $F_"k−1"$ and blocks $s$, which is then used to strengthen the frames $F_0, dots, F_k$ of the FRS. The algorithm terminates if either a counterexample is found or a frame is determined to be an inductive invariant that proves the property.

== If that is not enough

- *Avy* - An interpolating IC3 (Y. Vizel, A. Gurfinkel: Interpolating Property Directed Reachability. CAV 2014)

- IC3 full algorithm (a lot of different literature, for example: 
  - Somenzi_and_Bradley_2011_IC3_Where_monolithic_and_incremental_meet
  - Bradley (2012)  - Understanding IC3)
  
- #link("https://fmv.jku.at/hwmcc20/")[Hardware model checking competition(HWMCC)]

== Sources

- https://ieeexplore.ieee.org/document/7225110/figures#figures
- https://lara.epfl.ch/w/_media/sav08/mcmillaninterpolation.pdf