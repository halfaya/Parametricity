{-# OPTIONS --without-K #-}

module StdLib where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Agda.Builtin.Bool     public
open import Agda.Builtin.Nat      public
open import Agda.Builtin.List     public
open import Agda.Builtin.Equality public

ℕ : Set
ℕ = Nat

--------

map : {ℓ m : Level} {A : Set ℓ} {B : Set m} → (f : A → B) → List A → List B
map f []       = []
map f (a ∷ as) = f a ∷ map f as

--------

subst : {ℓ : Level} {A : Set ℓ} → (P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst P refl p = p

sym : {ℓ : Level} {A : Set ℓ} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {ℓ : Level} {A : Set ℓ} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl eq = eq

cong : {ℓ m : Level} {A : Set ℓ} {B : Set m}
       (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

--------

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixl 4 _×_
infixr 4 _,_

