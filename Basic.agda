{-# OPTIONS --safe -- #-}

module Basic where

open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Function.Base using (_$_)
open import Data.Unit.Base using (⊤ ; tt)


open import Semantics
open Model


record Prop (M : Model) : Set₁ where
  field
    val : W M → Set₀
    
open Prop public


_,_⊨_ : ∀ (M : Model) → W M → Prop M → Set₀
M , w ⊨ F = val F w

infixr 10 _,_⊨_


{-

Valid : ∀ (M : Model) → Prop M → Set₀
Valid M A = ∀ (w : W M) → M , w ⊨ A

⊨_ : (∀ (M : Model) → Prop M) → Set₁            Мне кажется, что эти определения излишние для нашего shallow embedding.
⊨ A = ∀ (M' : Model) → Valid M' (A M')        Так что можно пока их считать просто упражнением на формализацию  


infixr 9  ⊨_

-}

□_ : ∀ {M : Model} → Prop M → Prop M
□_ {M} F =
  record
    { val = λ w →
        ∀ w' →
        R M w w' →
        M , w' ⊨ F
    }


◇_ : ∀ {M : Model} → Prop M → Prop M
◇_ {M} F =
  record
    { val = λ w →
        Σ (W M) λ w' →
        R M w w' × M , w' ⊨ F
    }


~_ : ∀ {M : Model} → Prop M → Prop M
~_ {M} F =
  record
    { val = λ w →
        ¬ (M , w ⊨ F)
    }


_⇒_ : ∀ {M : Model} → Prop M → Prop M → Prop M
_⇒_ {M} A B =
  record
    { val = λ w →
        M , w ⊨ A →
        M , w ⊨ B
    }


_∧_ : ∀ {M : Model} → Prop M → Prop M → Prop M
_∧_ {M} A B =
  record
    { val = λ w →
        (M , w ⊨ A) ×
        (M , w ⊨ B)
    }


_∨_ : ∀ {M : Model} → Prop M → Prop M → Prop M
_∨_ {M} A B =
  record
    { val = λ w →
        (M , w ⊨ A) ⊎
        (M , w ⊨ B)
    }


_⇔_ : ∀ {M : Model} → Prop M → Prop M → Prop M
_⇔_ {M} A B =
  (A ⇒ B) ∧ (B ⇒ A)

{- Красивые первопорядковые модальные кванторы -}

∀ᵐ[_] : ∀ {M : Model} → (D M → Prop M) → Prop M
∀ᵐ[ P ] =
  record
    { val = λ w →
        ∀ d →
        val (P d) w
    }


∃ᵐ[_] : ∀ {M : Model} → (D M → Prop M) → Prop M
∃ᵐ[ P ] =
  record
    { val = λ w →
        Σ _ λ d →
        val (P d) w
    }


_∙_ : ∀ {M : Model} (P : D M → Prop M) → (a : W M → D M) → Prop M
P ∙ a = record { val = λ w → val (P (a w)) w }

{- Помогает заменить лямбда-абстракцию Фиттинга и Мендельсона и выразить суждения об именах de dicto -}

_>_ : ∀ {M : Model} → Prop M → Prop M → Prop M
_>_ {M} A B =
  record
    { val = λ w →
        ∀ w' →
        F M (val A) w w' →
        M , w' ⊨ B
    }

_=ᵐ_ : ∀ {M : Model} → D M → D M → Prop M
A =ᵐ B = record {val = λ w → A ≡ B}

infixr 60 _=ᵐ_
infixr 100 _∙_
infixr 100 ~_
infixr 100 □_
infixr 100 ◇_
infixr 50 _∨_
infixr 40 _∧_
infixr 30 _⇒_
infixr 20 _⇔_
infixr 15 _>_
infixr 100 ∀ᵐ[_]
infixr 100 ∃ᵐ[_]

Reflexive : ∀ (M : Model) → Set₀
Reflexive (M) = ∀ w → R M w w


Symmetric : ∀ (M : Model) → Set₀
Symmetric (M) = ∀ {w w'} → R M w w' → R M w' w


Transitive : ∀ (M : Model) → Set₀
Transitive (M) = ∀ {w w' w''} → R M w w' → R M w' w'' → R M w w''


Serial : ∀ (M : Model) → Set₀
Serial (M) = ∀ w → Σ (W M) λ w' → R M w w'


Euclidean : ∀ (M : Model) → Set₀
Euclidean (M) = ∀ {w v u} → R M w v → R M w u → R M v u

Universal : ∀ (M : Model) → Set₀
Universal M = ∀ w w' → R M w w'

data Worlds-1 : Set₀ where
 world-one : Worlds-1

data Worlds-2 : Set₀ where
 world-one : Worlds-2
 world-two : Worlds-2

data Worlds-3 : Set₀ where
 world-one : Worlds-3
 world-two : Worlds-3
 world-three : Worlds-3




