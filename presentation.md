# Schmitty the Solver

### by Wen Kokke

#### with contributions from Ulf Norell, and hopefully soon, you!

---------------------------------------------------------------------------------

# Let’s solve some stuff!

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

_ : ∀ x y z → x + (y + z) ≡ (x + y) + z
_ = solveZ3

_ : ∀ x → (x + 2) * (x + -2) ≡ x * x - 4
_ = solveZ3

_ : ∃[ z ] (∀ n → z * n ≡ 0)
_ = solveZ3
```

^
Great, let's get to solving!

^
I've imported the theory for integer arithmetic, and put up a few equations:
- associativity of plus;
- distributivity'ish;
- finding zero.

^
This compiles, and that's cool!

^
"What do the error messages look like?"

---------------------------------------------------------------------------------

# What if we make a mistake?

```
_ : (x y : ℤ) → x ≤ y → x ≡ y
_ = solveZ3
```
```
Found counter-example:
x = + 0
y = + 1
refuting (z : + 0 ≤ + 1) → + 0 ≡ + 1
when checking that the expression unquote solveZ3 has type
(x y : ℤ) → x ≤ y → x ≡ y
```

^
Let's say we ask Z3 to prove something that... isn't true.

^
We get a message from Z3 showing us the counter-example!

---------------------------------------------------------------------------------

# What is a SMT-LIB?

---------------------------------------------------------------------------------

# What is a SMT-LIB?

1. A language for solver input and output.
2. Theories to be supported by solvers: arrays, fixed-size bit vectors, floats, ints, reals, ints and reals, Unicode strings, etc …
3. Logics to be supported by solvers, e.g., “quantifier-free linear integer arithmetic with equality and uninterpreted functions”
   (or `QF_EUFLIA` for robots)

---------------------------------------------------------------------------------

# What is a Schmitty?

---------------------------------------------------------------------------------

# What is a Schmitty?

1. an embedding of SMT-LIB in Agda
3. integration with Agda reflection
2. integration with solvers via system calls

---------------------------------------------------------------------------------

# What is a Schmitty? — Terms

Sorts, Literals, and Identifiers vary by theory:

```
mutual
  data Term : Set where
    var    : (n : ℕ) → Term
    lit    : (l : Literal) → Term
    app    : (x : Identifier) (xs : Args) → Term
    forAll : (σ : Sort) (x : Term) → Term
    exists : (σ : Sort) (x : Term) → Term

  Args = List Term
```

^
First, let's talk about SMT-LIB terms.

^
We've got:
- variables and application;
- *no lambdas*;
- *literals*, depending on the theory;
- *some* primitive identifiers, depending on the theory;
- universal/existential quantifiers.
That's all.

---------------------------------------------------------------------------------

# What is a Schmitty? — Terms

Except… it’s well-sorted by construction:

```
mutual
  data Term (Γ : Ctxt) : (σ : Sort) → Set where
    var    : (x : Γ ∋ σ) → Term Γ σ
    lit    : (l : Literal σ) → Term Γ σ
    app    : (x : Identifier Σ) (xs : Args Γ (ArgSorts Σ)) → Term Γ σ
    forAll : (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    exists : (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL

  Args : (Γ Δ : Ctxt) → Set
  Args Γ Δ = All (λ σ → Term Γ σ) Δ
```

^
Except… it’s all a bit more complicated, since the embedding is well-sorted by construction.

^
We add contexts Γ, which are lists of sorts, and signatures Σ, which are function signatures: one sort per argument, and one sort for the return value.

---------------------------------------------------------------------------------

# What is a Schmitty? — Commands & Scripts

There's commands and scripts as well:

```
data Command : Set where
  set-logic     : (l : Logic) → Command
  declare-const : (σ : Sort) → Command
  assert        : Term → Command
  check-sat     : Command
  get-model     : Command

Script = List Command
```

^
SMT-LIB also has commands and script, which are just lists of commands.

^
`set-logic`: set the SMT-LIB logic
`declare-const`: introduce a top-level variable
`assert`: give Z3 an assertion
`check-sat`: tell Z3 to check the satisfiability of all the assertions
`get-model`: tell Z3 to return a model

^
Very much a subset of all SMT-LIB commands.

---------------------------------------------------------------------------------

# What is a Schmitty? — Commands & Scripts

Except… They're a wee bit more complicated:

```
data Command (Γ : Ctxt) : (δΓ : Ctxt) (δΞ : OutputCtxt) → Set where
  set-logic     : (l : Logic) → Command Γ [] []
  declare-const : (n : String) (σ : Sort) → Command Γ (σ ∷ []) []
  assert        : Term Γ BOOL → Command Γ [] []
  check-sat     : Command Γ [] (SAT ∷ [])
  get-model     : Command Γ [] (MODEL Γ ∷ [])

data Script (Γ : Ctxt) : (Γ′ : Ctxt) (Ξ : OutputCtxt) → Set where
  []  : Script Γ Γ []
  _∷_ : Command Γ δΓ δΞ → Script (δΓ ++ Γ) Γ′ Ξ → Script Γ Γ′ (δΞ ++ Ξ)
```

^
Script types have two params:
`Γ`: types before evaluating the script;
`Γ′`: types after evaluating the script;
`Ξ`: types of outputs produced by Z3.

^
Command types have three params:
`Γ`: typing context for command;
`δΓ`: new types bound;
`δΞ`: new outputs produced.

^
Output types:
- SAT (sat, unsat, unknown); or
- MODEL (environment scoped under Γ).

---------------------------------------------------------------------------------

# What is a Schmitty? — Core Theory

```
data CoreSort : Set where
  BOOL : CoreSort

data CoreLiteral : CoreSort → Set where
  -- false and true are identifiers

data CoreId : (Φ : Sig φ) → Set where
  false true         : CoreId (Op₀ BOOL)
  not                : CoreId (Op₁ BOOL)
  implies and or xor : CoreId (Op₂ BOOL)

CoreValue : CoreSort → Set
CoreValue BOOL = Set
-- slightly more complex, due to Type∈Type
```

^
We instantiate the `Term` and `Script` types with a theory.

^
A theory contains:
- Sorts;
- Literals;
- Identifiers;
- Mapping from Sorts to Agda types.

---------------------------------------------------------------------------------

# What is a Schmitty? — Ints Theory

[.column]
```
data Sort : Set where
  CORE : (φ : CoreSort) → Sort
  INT  : Sort

data Literal : Sort → Set where
  core : CoreLiteral φ
       → Literal (CORE φ)
  nat  : ℕ → Literal INT

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value INT      = ℤ
```

[.column]
```
data Id : (Σ : Sig σ) → Set where

  -- include core identifiers
  core : CoreId Φ → Id (map CORE Φ)

  -- equality, inequality, and ite
  -- are a part of the core theory
  eq neq : Id (Rel INT)
  ite    : Id (BOOL ∷ σ ∷ σ ↦ σ)

  -- theory of integer arithmetic
  not abs             : Id (Op₁ INT)
  sub add mul div mod : Id (Op₂ INT)
  leq lt geq gt       : Id (Rel INT)
```

^
The module defining term takes a `Theory`, but what's in a theory?

^
Essentially, Sorts, Literals, and Identifiers, plus functions that tell Agda various things about these things, such as how to parse and print them.

^
Here's the types for the Core theory, essentially propositional logic.
Every SMT-LIB theory extends the Core theory.

^
Note, we're calling it BOOL here, but this'll actually end up being linked to Agda's Set.

---------------------------------------------------------------------------------

# How does a Schmitty?

## (in seven steps)

---------------------------------------------------------------------------------

# How does a Schmitty? — ① Reflection

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal

_ = pi (vArg (def (quote ℤ) [])) $ abs "x"
  $ pi (vArg (def (quote ℤ) [])) $ abs "y"
  $ def (quote _≡_)
    $ hArg (def (quote Level.zero) [])
    ∷ hArg (def (quote ℤ) [])
    ∷ vArg (def (quote _+_) (vArg (var 1 []) ∷ (vArg (var 0 []) ∷ [])))
    ∷ vArg (def (quote _+_) (vArg (var 0 []) ∷ (vArg (var 1 []) ∷ [])))
    ∷ []
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ② Raw Script

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript

_ = declare-const "x" (TERM (def (quote ℤ) []))
  ∷ declare-const "y" (TERM (def (quote ℤ) []))
  ∷ assert ( app₁ (quote ¬_) $ app₂ (quote _≡_)
                             $ app₂ (quote _+_) (# 1) (# 0)
                             ∷ app₂ (quote _+_) (# 0) (# 1) )
  ∷ get-model
  ∷ []
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ③ Check Script

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript ∘ checkRawScript

_ = declare-const "x" INT
  ∷ declare-const "y" INT
  ∷ assert ( app₁ neq
           $ app₂ eq
               $ app₂ add (# 1) (# 0)
               ∷ app₂ add (# 0) (# 1)
           )
  ∷ get-model
  ∷ []
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ④ Print Script

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript ∘ checkRawScript ∘
    showScript

"(declare-const x_0 Int)
 (declare-const y_1 Int)
 (assert (not (= (+ x_0 y_1) (+ y_1 x_0))))
 (check-sat)
 (get-model)"
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ⑤ System Call

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript ∘ checkRawScript ∘ 
    showScript ∘ execTC

"unsat"
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ⑥ Parse Outputs

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript ∘ checkRawScript ∘ 
    showScript ∘ execTC ∘ parseOutputs

_ : Sat
_ = unsat -- that’s what we want!
```

---------------------------------------------------------------------------------

# How does a Schmitty? — ⑦ Quote Outputs

```
_ : ∀ x y → x + y ≡ y + x
_ = solveZ3

  ↓ quoteGoal ∘ reflectToRawScript ∘ checkRawScript ∘ 
    showScript ∘ execTC ∘ parseOutputs ∘ quoteOutputs

_ : ∀ x y → x + y ≡ y + x
_ = λ x y → because "z3" (x + y ≡ y + x)
```

---------------------------------------------------------------------------------

# What else do we have?

---------------------------------------------------------------------------------

# What else do we have?

- Backends for _Z3_ and _CVC4_
- Theory of _integers_ linked to Agda integers
- Theory of _real numbers_ linked to Agda floats
- Proofs which compute (when fully applied)

---------------------------------------------------------------------------------

# Where to go from here?

---------------------------------------------------------------------------------

# Roadmap (easy)

[.text: text-scale(0.75)]

- Add backends for _other SMT-LIB compliant solvers_
- Add _pseudo-sort for naturals_ to the integer theory
- Add theory of _real arithmetic_ linked to Agda rational numbers
- Add theory of _floating-point numbers_ linked to Agda floats
- Add theory of _strings_ linked to Agda strings
- Add _error reporting_ to the parsers
- Provide witnesses for top-level existentials

---------------------------------------------------------------------------------

# Roadmap (moderate)

[.text: text-scale(0.75)]

- Add theory of _sequences_ linked to _Agda lists_
- Add theory of _uninterpreted functions_ linked to Agda names
- Add theory of _regular expressions_ linked to aGdaREP
- Add theory of _algebraic datatypes_ linked to Agda datatypes
- Add theory of _arrays_ linked to Haskell arrays
- Add support for _combined theories_
- Add support for _logic declarations_

---------------------------------------------------------------------------------

# Roadmap (hard)

[.text: text-scale(0.75)]

- Add proof checking for Z3 proofs,
  cf. “Proof Reconstruction for Z3 in Isabelle/HOL”

```
unsat
((proof
    (let ((@x36 (monotonicity 
        (rewrite (= (= (+ x_0 y_1) (+ y_1 x_0)) true)) 
        (= (not (= (+ x_0 y_1) (+ y_1 x_0))) (not true)))))
    (let ((@x40 (trans @x36 
        (rewrite (= (not true) false)) 
        (= (not (= (+ x_0 y_1) (+ y_1 x_0))) false))))
    (mp (asserted (not (= (+ x_0 y_1) (+ y_1 x_0)))) @x40 false)))))
```
