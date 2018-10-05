{-# OPTIONS --without-K #-}

module SystemF where

open import StdLib

data Var : Set where
  var : ℕ → Var

data Type : Set where
  var  : Var → Type
  _⟶_  : Type → Type → Type
  ∀[_]_ : Var → Type → Type

data Term : Set where
  base : Term
  
