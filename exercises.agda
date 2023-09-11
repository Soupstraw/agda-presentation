open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 30 _∷_

⟦_⟧ : ∀ {A} → A → List A
⟦_⟧ = _∷ []

_++_ : ∀ {A} → List A → List A → List A
xs ++ ys = {!!}











reverse : ∀ {A} → List A → List A
reverse xs = {!!}












[]-++-right-unit : ∀ {A} {xs : List A} → xs ≡ xs ++ []
[]-++-right-unit = {!!}












++-assoc : ∀ {A} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys zs = {!!}












reverse-++ : ∀ {A} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ xs ys = {!!}
