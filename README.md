# $S_{\infty}$

[Gödel's second incompletenes theorem](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems#Second_incompleteness_theorem) states that the impossibility to prove consistency of formal arithmetic within the formal arithmetic itself. $S_{\infty}$ is a first-order logic and is one of the calculi used for [Gentzen's consistency proof](https://en.wikipedia.org/wiki/Gentzen%27s_consistency_proof) of first-order arithmetic.

## Syntax

$S_{\infty}$ contains the following logical and non-logical symbols.

1. Non-logical symbols (metavariable: $\theta$)
   1. Zero $(0)$, nullary
   2. Successor $(')$, unary
   3. Plus $(+)$, binary
   4. Times $(*)$, binary
   5. Quantifiable (either free or bound) variables (e.g. $x, y, z$)
2. Logical symbols (in order of precedence: highest to lowest)
   1. Equality $(=)$, binary
   2. Negation $(\neg)$, unary
   3. Disjunction $(\vee)$, binary
   4. Universal quantifier $(\forall)$

An example of a well-formed expression in $S_{\infty}$ would be
* $\forall a \: . \: \neg \forall b \: . \: \neg a \cdot b = a$

This is "equivalent" to the statement that for every $a$ there exists a $b$ such that $a \cdot b = a$

## Deductive system

### Axioms

An axiom in $S_{\infty}$ can only be of two forms.
* $\theta_1 = \theta_2$
* $\neg \theta_1 = \theta_2$

Where $\theta_i$ are terms without variables.

Addition and multiplication are defined canonically and are evaluated.
1. If the result is a reflexivity, it's an axiom. For example, $1' \cdot 3 + 1 = 3 + 2''$ is an axiom, because $7 = 7$.
2. If the result is a negation of an irreflexivity, it's an axiom. For example, $\neg 9' = 2''' * 2$ is an axiom, because $\neg 9 = 10$.

### Rules of inference

#### Preface

In the familiar propositional and predicate calculi we have the following structure of a judgment.
$$\Gamma \vdash \alpha$$
$\Gamma$ is the context, i.e. a set, possibly empty, of hypotheses assumed to hold. $\alpha$ is the formula to be proven. Most of the time the context contains a finite number of formulas
$$\gamma_1, \gamma_2, \dots, \gamma_k \vdash \alpha$$
and is equivalent, by the Deduction theorem (sans the limitations preventing the transfer of the hypothesis from the context into the antecedent of the implication in the predicate calculus), to
$$\vdash \gamma_1 \to \gamma_2 \to \dots \to \gamma_k \to \alpha \\ \vdash \gamma_1 \wedge \gamma_2 \wedge \dots \wedge \gamma_k \to \alpha$$

In $S_{\infty}$ we have neither the logical conjunction nor the logical implication. The notation used in this library is reminiscent to the usual judgments, except the turnstile $\vdash$ is replaced with the big vee $\bigvee$ and the term _hypothesis_ is replaced with **disjunct**.
$$\Delta \bigvee \alpha$$
Suppose, once again, we have a finite number of disjuncts.
$$\delta_1, \delta_2, \dots, \delta_k \bigvee \alpha$$
This is equivalent to the only other contextless form.
$$\delta_1 \vee \delta_2 \vee \dots \vee \delta_k \vee \alpha$$

#### Structural rules

Since organizing the desired look of the rules of inference is seemingly impossible in Markdown LaTeX, pretend the $\therefore$ symbol is the inference line. The premises are written in each separate line.

1. **Joining** the top two disjuncts.
   $$\Delta, \delta_1, \delta_2 \bigvee \alpha \\ \therefore \\ \Delta, \delta_1 \vee \delta_2 \bigvee \alpha$$
2. **Splitting** the top two disjuncts
   $$\Delta, \delta_1 \vee \delta_2 \bigvee \alpha \\ \therefore \\ \Delta, \delta_1, \delta_2 \bigvee \alpha$$
3. Moving the top disjunct **out of** the context.
   $$\Delta, \delta \bigvee \alpha \\ \therefore \\ \Delta \bigvee \delta \vee \alpha$$
4. Moving the top disjunct **into** the context.
   $$\Delta \bigvee \delta \vee \alpha \\ \therefore \\ \Delta, \delta \bigvee \alpha$$
5. **Swapping** the top disjunct with the formula.
   $$\Delta, \delta \bigvee \alpha \\ \therefore \\ \Delta, \alpha \bigvee \delta$$
6. **Removing the duplicate** formula from the top of the context.
   $$\Delta, \alpha \bigvee \alpha \\ \therefore \\ \Delta \bigvee \alpha$$

#### Strong rules

1. **Weakening**
   $$\Delta \bigvee \delta \\ \therefore \\ \Delta, \delta \bigvee \alpha$$
2. **De Morgan's rule**
   $$\Delta \bigvee \neg \alpha \\ \Delta \bigvee \neg \beta \\ \therefore \\ \Delta \bigvee \neg \left( \alpha \vee \beta \right)$$
3. **Double negation introduction (DNI)**
   $$\Delta \bigvee \alpha \\ \therefore \\ \Delta \bigvee \neg \neg \alpha$$
4. **The $\neg \forall$-rule**
   $$\Delta \bigvee \neg \alpha \left[ x \coloneqq \theta \right] \\ \therefore \\ \Delta \bigvee \neg \forall x \: . \: \alpha$$

#### Induction

The infinite induction rule is a special rule that *should* look like this.

$$\Delta \bigvee \alpha \left[ x \coloneqq 0 \right] \\ \Delta \bigvee \alpha \left[ x \coloneqq 1 \right] \\ \vdots \\ \therefore \\ \Delta \bigvee \forall x \: . \: \alpha$$

However, given it's impossible to actually enumerate all the premises without spending an infinite amount of time, the implementation of this rule utilizes the Lean-specific universal quantification on the `Nat`-type in its only premise.

#### Section

The section rule lets us eliminate a formula if both it and its negation are present as two disjuncts in two separate nodes of the proof tree.

$$\Delta \bigvee \zeta \vee \alpha \\ \Delta \bigvee \neg \alpha \vee \delta \\ \therefore \\ \Delta \bigvee \zeta \vee \delta$$

The current implementation of the section rule requires the context be the same. Both $\zeta$ and $\delta$ can be considered parts of their respective contexts, even though they are outside of them, which showcases the implementation flaw.
