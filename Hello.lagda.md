% Gentle introduction to Agda
% Joosep Jääger
% September 13, 2022

## Recommended reading

 - [Programming Language Foundations in Agda by Philip Wadler](https://plfa.github.io/)
 - [Propositions as Types by Philip Wadler](https://www.youtube.com/watch?v=IOiZatlZtGU)

## Follow along

<https://agdapad.quasicoherent.io/>

<https://github.com/Soupstraw/agda-presentation>

## Imports

```agda
-- `open import` is the same as a regular import in Haskell
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- Notice the use of semicolon when importing with `using` syntax
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String
```

## Familiar syntax

```agda
-- Notice the single colon instead of Haskell's double colon.
-- The function arrows are unicode

-- Agda-input reference
-- \->    →
-- \bN    ℕ

double : ℕ → ℕ
double x = x + x
```

## Mixfix operators

```agda
-- NB! Whitespace between the variable and the operator is mandatory!

-- \^2    ²

_² : ℕ → ℕ
x ² = x * x
```

## 90% Less sugar*

```agda
-- If-then-else can be written as a function, no need for syntactic sugar
if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else _ = x
if false then _ else x = x

-- `{A : Set}` can be thought of as Haskell's `forall a.`

-- `Set` is actually `Type` or `*` in Haskell
```

## Data types

```agda
-- This will look familiar if you've worked with GADTs before
data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 30 _∷_

someList = 1 ∷ 2 ∷ []
```

## Records

```agda
record Person : Set where
  -- `constructor` is optional
  constructor _,age_
  field
    name : String
    age : ℕ

personA = "Mati" ,age 25

personB = record
  { name = "Kati"
  ; age = 30
  }
```

## Writing a `reverse` function

```agda
-- First we need some helpers

-- Singleton list
⟦_⟧ : ∀ {A} → A → List A
-- ⟦ x ⟧ = x ∷ []
⟦_⟧ = _∷ []

-- List concatenation
_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

-----

```agda
reverse : ∀ {A} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ ⟦ x ⟧
```

## The problem

```agda
-- Our `reverse` isn't the only function that inhabits this type:

mystery1 : ∀ {A} → List A → List A
mystery1 x = []

mystery2 : ∀ {A} → List A → List A
mystery2 x = x

mystery3 : ∀ {A} → List A → List A
mystery3 [] = []
mystery3 (x ∷ xs) = xs ++ ⟦ x ⟧
```

-----

We have to constrain `reverse` so we can be sure what it says it does

. . .

To do that we will prove some properties using our implementation of `reverse`

. . .

What does it mean to prove something about our program?

## Curry-Howard correspondence

| Haskell       | Agda        | Mathematical logic |
|---------------|-------------|--------------------|
| Void          | ⊥           | ⊥                  |
| ()            | ⊤           | ⊤                  |
| (P, Q)        | P × Q       | P ∧ Q              |
| Either P Q    | P ⊎ Q       | P ∨ Q              |
| P -> Q        | P → Q       | P ⊃ Q              |

-----

Types are propositions

Proofs are programs

. . .

To prove something in Agda means to show that a type is inhabited by constructing a value of that type

## Propositional equality

Propositional equality is denoted by `_≡_`.

. . .

It has a single constructor `refl : A ≡ A`


## Transitivity

Let's prove this interactively

P ≡ Q ⇒ Q ≡ R ⇒ P ≡ R

## Monoid

Set `A` with an operation ⊗ and a unit element e ∈ A is a monoid
iff the following properties are satisfied

|                           |                        |
|---------------------------|------------------------|
| e ⊗ x ≡ x ⊗ e ≡ x         |  (left/right identity) |
| (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z) |  (associativity)       |



## Right identity

    []-++-right-unit : ∀ {A} {xs : List A} → xs ≡ xs ++ []

Let's prove this interactively

## Right identity

```agda
[]-++-right-unit : ∀ {A} {xs : List A} → xs ≡ xs ++ []
[]-++-right-unit {_} {[]} = refl
[]-++-right-unit {_} {x ∷ xt} = cong (x ∷_) []-++-right-unit
```

## Associativity

    ++-assoc : ∀ {A} (xs ys zs : List A)
      → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

## Associativity

```agda
++-assoc : ∀ {A} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {_} [] y z = refl
++-assoc {_} (x ∷ x₁) y z = cong (x ∷_) (++-assoc x₁ y z)
```

## A property of `reverse`

    reverse-++ : ∀ {A} (xs ys : List A)
      → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

## A property of `reverse`

```agda
reverse-++ : ∀ {A} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] y = []-++-right-unit
reverse-++ (x ∷ x₁) y rewrite sym (++-assoc (reverse y) (reverse x₁) ⟦ x ⟧) =
  cong (_++ ⟦ x ⟧) (reverse-++ x₁ y)
```


