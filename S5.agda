{-# OPTIONS --safe -- #-}

module S5 where

open import Data.Empty
open import Data.Product
open import Data.Sum renaming ([_,_] to ⊎-elim)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
open import Function.Base using (_$_)
open import Data.Unit.Base using (⊤ ; tt)
open import Semantics
open import Basic
open Model

record S5_Model : Set₁ where
 field
  Basic : Model
  Universal_S5 : Universal Basic

open S5_Model

𝐖-S5 : S5_Model → Set₀
𝐖-S5 M = 𝐖 (Basic M)

𝐃-S5 : S5_Model → Set₀
𝐃-S5 M = 𝐃 (Basic M)

𝐑-S5 : (M : S5_Model) → 𝐖-S5 M → 𝐖-S5 M → Set₀
𝐑-S5 M = 𝐑 (Basic M)

¬□impl◇ : ∀ (M : S5_Model) (w : 𝐖-S5 M) (P : Prop (Basic M)) → ((Basic M) , w ⊨ □ P) → ((Basic M) , w ⊨ ◇ P)
¬□impl◇ M w P H = Goal where

 H-unfolded : ∀ w' → 𝐑-S5 M w w' → (Basic M) , w' ⊨ P
 H-unfolded = H

 Goal =  w , ( Universal_S5 M w w , H w (Universal_S5 M w w))
