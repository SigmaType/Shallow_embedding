{-# OPTIONS --safe -- #-}

module Basic_lemmas where

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


K_axiom : ∀ (M : Model) (w : 𝐖 M) (A B : Prop M) → M , w ⊨ □ (A ⇒ B) →  M , w ⊨ □ A ⇒ □ B
K_axiom M w A B H1 H2 = Goal where

 H1_unf : ∀ w' →  𝐑 M w w' → M , w' ⊨ A ⇒ B
 H1_unf = H1

 H2_unf :  ∀ w' →  𝐑 M w w' → M , w' ⊨ A
 H2_unf = H2

 Goal : ∀ w' →  𝐑 M w w' → M , w' ⊨ B
 Goal = λ w' RMww' → (H1_unf w' RMww') (H2_unf w' RMww')


Nec : ∀ (M : Model) → (A : Prop M) → (∀ w → M , w ⊨ A) → (∀ w → M , w ⊨ □ A)
Nec M A H w = Goal where

 Goal :  ∀ w' →  𝐑 M w w' → M , w' ⊨ A
 Goal = λ w' RMww' → H w'

>_weakness_right : ∀ (M : Model) (w : 𝐖 M) (A B C : Prop M) → M , w ⊨ A > B → M , w ⊨ A > (B ∨ C)
>_weakness_right M w A B C H = Goal where

 H_unf : ∀ w' → 𝐅 M (val A) w w' → M , w' ⊨ B
 H_unf = H

 Goal : ∀ w' → 𝐅 M (val A) w w' → M , w' ⊨ B ∨ C
 Goal = λ w' F → inj₁ (H_unf w' F)

¬□impl◇ : ¬ ∀ (M : Model) (w : 𝐖 M) (P : Prop M) → (M , w ⊨ □ P) → (M , w ⊨ ◇ P)
¬□impl◇ H = Goal where

 Countermodel = record
   {𝐖 = Worlds-1 ;
    witness-w = world-one ;
    𝐃 = Worlds-1 ;
    witness-d = world-one ;
    𝐑 = λ _ _ → ⊥ ;
    𝐅 = λ _ _ _ → ⊥}

 P : Prop Countermodel
 P = record {val = λ _ → ⊥}

 Antecedent : Countermodel , world-one ⊨ □ P
 Antecedent world-one ()

 Consequent : ¬ (Countermodel , world-one ⊨ ◇ P)
 Consequent (w' ,(Rww' , ⊨P)) =  Rww'
 
 {- Раскрыли определение Countermodel , world-one ⊨ ◇ P -}
{- Отношение достижимости не выполняется, поэтому утверждение о нем можем взять как ⊥ -}

   
 Goal = Consequent (H Countermodel world-one P Antecedent)


lemma-1 : ¬ ∀ (M : Model) (w : 𝐖 M) (A B C : Prop M) → (M , w ⊨ A > B) → (M , w ⊨ A ∧ B > C)
lemma-1 H = Goal where

 F-countermodel : (Worlds-2 → Set₀) → Worlds-2 → Worlds-2 → Set₀
 F-countermodel P world-one world-one = ⊥
 F-countermodel P world-one world-two = P world-one → ⊥
 F-countermodel P world-two _ = ⊥

 Countermodel : Model
 Countermodel =
   record
     { 𝐖 = Worlds-2 ;
       witness-w = world-one ;
       𝐃 = Worlds-2 ;
       witness-d = world-two ;
       𝐑 = λ _ _ → ⊥ ;
       𝐅 = F-countermodel }

 A : Prop Countermodel
 A = record {val = λ _ → ⊤}

 B : Prop Countermodel
 B = record {val = λ _ → ⊥}

 C : Prop Countermodel
 C = record {val = λ _ → ⊥}

 Antecedent : Countermodel , world-one ⊨ A > B
 Antecedent world-one ()
 Antecedent world-two h = h tt

{- То есть по A из первого мира никакой мир не доступен, поэтому A > B выполняется -}

 Consequent : ¬ Countermodel , world-one ⊨ A ∧ B > C
 Consequent H1 =
   let
    L1 : Countermodel , world-two ⊨ C
    L1 = H1 world-two (λ (tt , false) → false)
    in L1

    
 {- Из Countermodel , world-one ⊨ A ∧ B > C получаем Countermodel , world-two ⊨ C, а это противоречит истинностному значению C -}
    
 Goal : ⊥
 Goal = Consequent (H Countermodel world-one A B C Antecedent)


Barcan : ∀ (M : Model) (w : 𝐖 M) (P : 𝐃 M → Prop M) → (M , w ⊨ ∀ᵐ[ (λ d → □ (P d)) ]) → (M , w ⊨ □ ∀ᵐ[ P ])
Barcan M w P H w' R d = Goal where

 H-unfolded :  ∀ d → M , w ⊨ □ (P d)
 H-unfolded = H

 Goal = H d w' R

 {- Создадим инфраструктуру натуральной дедукции. Да, доказательства тривиальные. Зато теперь можно будет писать рассуждения более
 привычным образом-}

imp_intro : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} → (M , w ⊨ A → M , w ⊨ B) →  M , w ⊨ A ⇒ B
imp_intro {M} {w} {A} {B} H H1 = H H1

imp_elim : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A ⇒ B →  M , w ⊨ A  →  M , w ⊨ B
imp_elim{M} {w} {A} {B} H H1 = H H1

and_intro :  ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ B  →  M , w ⊨ A ∧ B
and_intro{M} {w} {A} {B} H H1 = H , H1

and_elim1 : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A ∧ B →  M , w ⊨ A  
and_elim1 {M} {w} {A} {B} (a , b) = a

and_elim2 : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A ∧ B →  M , w ⊨ B  
and_elim2 {M} {w} {A} {B} (a , b) =  b

or_elim : ∀ {M : Model} {w : 𝐖 M} {A B C : Prop M} →  M , w ⊨ A ⇒ C  →  M , w ⊨ B ⇒ C →  M , w ⊨ A ∨ B ⇒ C
or_elim {M} {w} {A} {B} {C} H H1 H2 = ⊎-elim case1 case2 H2 where

 case1 = λ Hypo → H Hypo
 case2 = λ Hypo → H1 Hypo

or_intro1 : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ A ∨ B
or_intro1{M} {w} {A} {B} H = inj₁ H

or_intro2 : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ B  →  M , w ⊨ A ∨ B
or_intro2{M} {w} {A} {B} H = inj₂ H

neg_intro : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ B →  M , w ⊨ ~ B →  M , w ⊨ ~ A
neg_intro {M} {w} {A} {B} H H1 H2 H3 = H2 H1

neg_elim : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ ~ A  →  M , w ⊨ B
neg_elim {M} {w} {A} {B} H H1 = ⊥-elim (H1 H)

box_intro :  ∀ {M : Model} {w : 𝐖 M} {A : Prop M} →  (∀ w' → 𝐑 M w w' → M , w' ⊨ A)  →  M , w ⊨ □ A
box_intro {M} {w} {A} H w' H1 = H w' H1

box_elim : ∀ {M : Model} {w w' : 𝐖 M} {A : Prop M} →  M , w ⊨ □ A  → 𝐑 M w w' →  M , w' ⊨ A
box_elim {M} {w}{w'} {A} H H1 = H w' H1

diamond_intro : ∀ {M : Model} {w w' : 𝐖 M} {A : Prop M} → 𝐑 M w w' → M , w' ⊨ A → M , w ⊨ ◇ A
diamond_intro {M} {w}{w'} {P} H H1 = w' , H , H1

diamond_elim : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} → M , w ⊨ ◇ A → (∀ w' → M , w' ⊨ A →  M , w ⊨ B) → M , w ⊨ B
diamond_elim {M} {w} {A} {B} (w' , Rww' , H1) H2 =  H2 w' H1

>_intro : ∀ {M : Model} {w : 𝐖 M} {A B : Prop M} →  (∀ w' → 𝐅 M (val A) w w' → M , w' ⊨ B)  →  M , w ⊨ A > B
>_intro {M} {w} {A} H w' H1 = H w' H1

>_elim : ∀ {M : Model} {w w' : 𝐖 M} {A B : Prop M} →  M , w ⊨ A > B  → 𝐅 M (val A) w w' →  M , w' ⊨ B
>_elim {M} {w}{w'} {A} H H1 = H w' H1

all_intro : ∀ {M : Model} {w : 𝐖 M} {P : 𝐃 M → Prop M} → (∀ d → M , w ⊨ P d)  →  M , w ⊨ ∀ᵐ[ P ]
all_intro {M}{w}{P} H d = H d

all_elim :  ∀ {M : Model} {w : 𝐖 M} {P : 𝐃 M → Prop M} (d :  𝐃 M) →  M , w ⊨ ∀ᵐ[ P ] → M , w ⊨ P d
all_elim = λ d H → H d

ex_intro :  ∀ {M : Model} {w : 𝐖 M} {P : 𝐃 M → Prop M} (d :  𝐃 M) →  M , w ⊨ P d → M , w ⊨ ∃ᵐ[ P ]
ex_intro {M} {w} {P} d H =  d , H

ex_elim : ∀ {M : Model} {w : 𝐖 M} {P : 𝐃 M → Prop M} {C : Prop M} → M , w ⊨ ∃ᵐ[ P ] → (∀ d → M , w ⊨ P d →  M , w ⊨ C) → M , w ⊨ C
ex_elim (d , Pd) H1 = H1 d Pd

