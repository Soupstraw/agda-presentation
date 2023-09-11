open import Relation.Binary.PropositionalEquality using (_≡_)

trans : ∀ {P Q R : Set} → P ≡ Q → Q ≡ R → P ≡ R
trans = {!!}



































open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.String

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 30 _∷_

⟦_⟧ : ∀ {A} → A → List A
⟦_⟧ = _∷ []

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : ∀ {A} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ ⟦ x ⟧

-- []-++-right-unit : ∀ {A} {xs : List A} → xs ≡ xs ++ []
-- []-++-right-unit = {!!}




























-- ++-assoc : ∀ {A} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
-- ++-assoc xs ys zs = {!!}























-- reverse-++ : ∀ {A} (xs ys : List A)
--   → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
-- reverse-++ xs ys = {!!}
