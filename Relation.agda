{-# OPTIONS --without-K #-}

module Relation where

open import StdLib

a = Bool × Bool

-- TODO: Why Set₁?
data _⇔_[_,_] : (A B : Set) → (a : A) → (b : B) → Set₁ where
  bool : (b : Bool) → Bool ⇔ Bool [ b , b ]
  nat  : (n : Nat) → ℕ ⇔ ℕ [ n , n ]
  prod : {A A' B B' : Set} {a : A} {a' : A'} {b : B} {b' : B'} →
         (aa' : A ⇔ A' [ a , a' ]) → (bb' : B ⇔ B' [ b , b' ]) → (A × B) ⇔ (A' × B') [ (a , b) , (a' , b') ]
  nil  : {A B : Set} → List A ⇔ List B [ [] , [] ]
  cons : {A B : Set} → {as : List A} → {bs : List B} →
         (a : A) → (b : B) → List A ⇔ List B [ as , bs ] → List A ⇔ List B [ a ∷ as , b ∷ bs ]
--  func : {A A' B B' : Set} → (f : A → B) → (g : A' → B') → ((a a' : A) → A ⇔ A [ a , a' ] → 
