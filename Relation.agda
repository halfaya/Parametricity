{-# OPTIONS --without-K #-}

module Relation where

open import StdLib

a = Bool × Bool

-- TODO: Why Set₁?
data _⇔_ : (A B : Set) → Set₁ where
  bool : Bool ⇔ Bool
  nat  : ℕ ⇔ ℕ
  prod : {A A' B B' : Set} → A ⇔ A' → B ⇔ B' → (A × B) ⇔ (A' × B')

infix 3 _⇔_
