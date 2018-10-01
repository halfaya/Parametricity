{-# OPTIONS --without-K #-}

module StdLib where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

--------

data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

map : {ℓ m : Level} {A : Set ℓ} {B : Set m} → (f : A → B) → List A → List B
map f []       = []
map f (a ∷ as) = f a ∷ map f as

--------

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

subst : {ℓ : Level} {A : Set ℓ} → (P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst P refl p = p

sym : {ℓ : Level} {A : Set ℓ} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {ℓ : Level} {A : Set ℓ} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl eq = eq

cong : {ℓ m : Level} {A : Set ℓ} {B : Set m}
       (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

