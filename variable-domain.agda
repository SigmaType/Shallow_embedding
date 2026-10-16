{-# OPTIONS --safe -- #-}

module variable-domain where

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
open import Propositional using (LEM ; DNE ; not-fall-exists ; nimpl-conj)
open Model

-- variable
negBarcan : Σ Model
  (λ M → Σ (W M)
  (λ w →
    Σ (D M → Prop M)
    (λ Ε →
    Σ (D M → Prop M)
    (
    λ P → (M , w ⊨ ∀ᵐ[ (λ d → (Ε d) ⇒ □ (P d)) ]) × ¬ (M , w ⊨ □ ∀ᵐ[ (λ d → (Ε d) ⇒ P d)])
    ))))

negBarcan = model-D2 , w0 , Ε , P , Ante , nConseq where
  data Worlds-D2 : Set₀ where
    w0 : Worlds-D2
    w1 : Worlds-D2
  
  data A-domain : Set₀ where
    a : A-domain

  RWorlds-D2 : Worlds-D2 → Worlds-D2 → Set₀
  RWorlds-D2 w0 w1 = ⊤
  RWorlds-D2 _ _ = ⊥

  model-D2 = record
    {W = Worlds-D2 ;
    witness-w = w0 ;
    D = A-domain ;
    witness-d = a ;
    R = RWorlds-D2 ;
    F = λ _ _ _ → ⊥}

  worldsΕ : (W model-D2) → Set₀
  worldsΕ w0 = ⊥
  worldsΕ w1 = ⊤

  Ε : D model-D2 → Prop model-D2
  Ε a = record {val = worldsΕ}

  worldsP : (W model-D2) → Set₀
  worldsP w0 = ⊥
  worldsP w1 = ⊥

  P : D model-D2 → Prop model-D2
  P a = record {val = worldsP}

  Ante : model-D2 , w0 ⊨ ∀ᵐ[ (λ d → (Ε d) ⇒ □ (P d)) ]
  Ante a w0Ea _ _ = ⊥-elim w0Ea

  nConseq : ¬ (model-D2 , w0 ⊨ □ ∀ᵐ[ (λ d → (Ε d) ⇒ P d)])
  nConseq = λ H →
    let
      H1 : ∀ (w' : W model-D2) → (R model-D2 w0 w') → model-D2 , w' ⊨ ∀ᵐ[ (λ d → (Ε d) ⇒ P d)]
      H1 = H
      H2 : ∀ (w' : W model-D2) → (R model-D2 w0 w') →
        ∀ (d : D model-D2) → (model-D2 , w' ⊨ Ε d) → (model-D2 , w' ⊨ P d)
      H2 = H1
    in
      H2 w1 tt a tt
  
negConBarcan : Σ Model
  (λ M → Σ (W M)
  (λ w →
    Σ (D M → Prop M)
    (λ Ε →
    Σ (D M → Prop M)
    (
    λ P → ¬ ((M , w ⊨ □ ∀ᵐ[ (λ d → (Ε d) ⇒ (P d)) ]) → (M , w ⊨ ∀ᵐ[ (λ d → (Ε d) ⇒ □ P d) ]))
    ))))

negConBarcan = model-D2 , w0 , Ε , P , (λ H → nConseq (H Ante)) where
  data Worlds-D2 : Set₀ where
    w0 : Worlds-D2
    w1 : Worlds-D2
  
  data A-domain : Set₀ where
    a : A-domain

  RWorlds-D2 : Worlds-D2 → Worlds-D2 → Set₀
  RWorlds-D2 w0 w1 = ⊤
  RWorlds-D2 _ _ = ⊥

  model-D2 = record
    {W = Worlds-D2 ;
    witness-w = w0 ;
    D = A-domain ;
    witness-d = a ;
    R = RWorlds-D2 ;
    F = λ _ _ _ → ⊥}

  worldsΕ : (W model-D2) → Set₀
  worldsΕ w0 = ⊤
  worldsΕ w1 = ⊥

  Ε : D model-D2 → Prop model-D2
  Ε a = record {val = worldsΕ}

  worldsP : (W model-D2) → Set₀
  worldsP w0 = ⊥
  worldsP w1 = ⊥

  P : D model-D2 → Prop model-D2
  P a = record {val = worldsP}

  Ante : model-D2 , w0 ⊨ □ ∀ᵐ[ (λ d → Ε d ⇒ P d) ]
  Ante w1 Rw0w1 a w1-Ea = w1-Ea

  nConseq : ¬ (model-D2 , w0 ⊨ ∀ᵐ[ (λ d → (Ε d) ⇒ □ P d) ])
  nConseq = λ H →
    let
      Ha : model-D2 , w0 ⊨ (Ε a) → (model-D2 , w0 ⊨ □ P a)
      Ha = H a
      boxPa : model-D2 , w0 ⊨ □ P a
      boxPa = Ha tt
      unf : ∀ (w : W model-D2) → R model-D2 w0 w → model-D2 , w ⊨ P a
      unf = boxPa
      w1-Pa : model-D2 , w1 ⊨ P a
      w1-Pa = unf w1 tt
    in
      w1-Pa
