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
open import Propositional using (LEM ; DNE ; not-fall-exists ; nimpl-conj)
open Model


K_axiom : ∀ (M : Model) (w : W M) (A B : Prop M) → M , w ⊨ □ (A ⇒ B) →  M , w ⊨ □ A ⇒ □ B
K_axiom M w A B H1 boxA = Goal where
  -- во всяком мире w', достижимом из w - unfold w' ⊨ □ (A ⇒ B)
  H1_unf : ∀ w' →  R M w w' → M , w' ⊨ A ⇒ B
  H1_unf = H1

  -- во всяком мире w', достижимом из w - unfold для w' ⊨ □ A
  boxA_unf :  ∀ w' →  R M w w' → M , w' ⊨ A
  boxA_unf = boxA

  -- во всяком мире w', достижимом из w - unfold для w' ⊨ □ B
  Goal : ∀ w' →  R M w w' → M , w' ⊨ B
  Goal = λ w' RMww' → (H1_unf w' RMww') (boxA_unf w' RMww')


Nec : ∀ (M : Model) → (A : Prop M) → (∀ w → M , w ⊨ A) → (∀ w → M , w ⊨ □ A)
Nec M A = λ (H : ∀ w → M , w ⊨ A) (w : W M) →
  let
    Goal :  ∀ w' →  R M w w' → M , w' ⊨ A
    Goal = λ w' _ → H w'
  in
    Goal


>_weakness_right : ∀ (M : Model) (w : W M) (A B C : Prop M) → M , w ⊨ A > B → M , w ⊨ A > (B ∨ C)
>_weakness_right M w A B C = λ (H : M , w ⊨ A > B) →
  let
    -- M , w ⊨ A > B  --> ∀ w' → F M (val A) w w' → M , w' ⊨ B
    H_unf : ∀ w' → F M (val A) w w' → M , w' ⊨ B
    H_unf = H
    Goal : ∀ w' → F M (val A) w w' → M , w' ⊨ B ∨ C
    Goal = λ w' F → inj₁ (H_unf w' F)
  in
    Goal

¬□impl◇ : ¬ ∀ (M : Model) (w : W M) (P : Prop M) → (M , w ⊨ □ P) → (M , w ⊨ ◇ P)
-- H : ∀ (M : Model) (w : W M) (P : Prop M) → (M , w ⊨ □ P) → (M , w ⊨ ◇ P)
¬□impl◇ H = Goal where

 Countermodel = record
   {W = Worlds-1 ;
    witness-w = world-one ;
    D = Worlds-1 ;
    witness-d = world-one ;
    R = λ _ _ → ⊥ ;
    F = λ _ _ _ → ⊥}

 P : Prop Countermodel
 P = record {val = λ _ → ⊥}

 Antecedent : Countermodel , world-one ⊨ □ P
 Antecedent =
   let
     unf : ∀ (w' : W Countermodel) → R Countermodel world-one w' →  Countermodel , w' ⊨ P
     unf = λ w' Rww' → ⊥-elim Rww'
   in
     unf

 Consequent : ¬ (Countermodel , world-one ⊨ ◇ P)
 Consequent (w' ,(Rww' , ⊨P)) =  Rww'
 
 {- Раскрыли определение Countermodel , world-one ⊨ ◇ P -}
{- Отношение достижимости не выполняется, поэтому утверждение о нем можем взять как ⊥ -}

   
 Goal = Consequent (H Countermodel world-one P Antecedent)


lemma-1 : ¬ ∀ (M : Model) (w : W M) (A B C : Prop M) → (M , w ⊨ A > B) → (M , w ⊨ A ∧ B > C)
lemma-1 H = Goal where

 F-countermodel : (Worlds-2 → Set₀) → Worlds-2 → Worlds-2 → Set₀
 F-countermodel P world-one world-one = ⊥
 F-countermodel P world-one world-two = P world-one → ⊥
 F-countermodel P world-two _ = ⊥

 Countermodel : Model
 Countermodel =
   record
     { W = Worlds-2 ;
       witness-w = world-one ;
       D = Worlds-2 ;
       witness-d = world-two ;
       R = λ _ _ → ⊥ ;
       F = F-countermodel }

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


Barcan : ∀ (M : Model) (w : W M) (P : D M → Prop M) → (M , w ⊨ ∀ᵐ[ (λ d → □ (P d)) ]) → (M , w ⊨ □ ∀ᵐ[ P ])
Barcan M w P H w' R d = Goal where

 H-unfolded :  ∀ d → M , w ⊨ □ (P d)
 H-unfolded = H

 Goal = H d w' R

 {- Создадим инфраструктуру натуральной дедукции. Да, доказательства тривиальные. Зато теперь можно будет писать рассуждения более
 привычным образом-}

imp_intro : ∀ {M : Model} {w : W M} {A B : Prop M} → (M , w ⊨ A → M , w ⊨ B) →  M , w ⊨ A ⇒ B
imp_intro {M} {w} {A} {B} H H1 = H H1

imp_elim : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A ⇒ B →  M , w ⊨ A  →  M , w ⊨ B
imp_elim{M} {w} {A} {B} H H1 = H H1

and_intro :  ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ B  →  M , w ⊨ A ∧ B
and_intro{M} {w} {A} {B} H H1 = H , H1

and_elim1 : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A ∧ B →  M , w ⊨ A
and_elim1 {M} {w} {A} {B} (a , b) = a

and_elim2 : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A ∧ B →  M , w ⊨ B  
and_elim2 {M} {w} {A} {B} (a , b) =  b

or_elim : ∀ {M : Model} {w : W M} {A B C : Prop M} →  M , w ⊨ A ⇒ C  →  M , w ⊨ B ⇒ C →  M , w ⊨ A ∨ B ⇒ C
or_elim {M} {w} {A} {B} {C} H H1 H2 = ⊎-elim case1 case2 H2 where

 case1 = λ Hypo → H Hypo
 case2 = λ Hypo → H1 Hypo

or_intro1 : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ A ∨ B
or_intro1{M} {w} {A} {B} H = inj₁ H

or_intro2 : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ B  →  M , w ⊨ A ∨ B
or_intro2{M} {w} {A} {B} H = inj₂ H

neg_intro : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ B →  M , w ⊨ ~ B →  M , w ⊨ ~ A
neg_intro {M} {w} {A} {B} H H1 H2 H3 = H2 H1

neg_elim : ∀ {M : Model} {w : W M} {A B : Prop M} →  M , w ⊨ A  →  M , w ⊨ ~ A  →  M , w ⊨ B
neg_elim {M} {w} {A} {B} H H1 = ⊥-elim (H1 H)

box_intro :  ∀ {M : Model} {w : W M} {A : Prop M} →  (∀ w' → R M w w' → M , w' ⊨ A)  →  M , w ⊨ □ A
box_intro {M} {w} {A} H w' H1 = H w' H1

box_elim : ∀ {M : Model} {w w' : W M} {A : Prop M} →  M , w ⊨ □ A  → R M w w' →  M , w' ⊨ A
box_elim {M} {w}{w'} {A} H H1 = H w' H1

neg_box : ∀ {M : Model} {w : W M} {A : Prop M} → (lem : LEM) →  M , w ⊨ ~ □ A  → M , w ⊨ ◇ ~ A
neg_box {M} {w} {A} lem H =
  let
    H_unfolded : ¬ (∀ w' → R M w w' → M , w' ⊨ A)
    H_unfolded = H
    H_exists : Σ (M .W) (λ x → ¬ (R M w x → M , x ⊨ A))
    H_exists = not-fall-exists lem H_unfolded
    w' , P = H_exists
    conj = nimpl-conj lem  P
  in
    w' , conj


diam_intro : ∀ {M : Model} {w w' : W M} {A : Prop M} → R M w w' → M , w' ⊨ A → M , w ⊨ ◇ A
diam_intro {M} {w}{w'} {P} H H1 = w' , H , H1

diam_elim : ∀ {M : Model} {w w' : W M} {A B : Prop M} → M , w ⊨ ◇ A → (∀ g → R M w g → M , g ⊨ A → M , w' ⊨ B) → M , w' ⊨ B
diam_elim {M} {w}{w'} {A} {B} (w0 , Rww0 , H1) H2 =  H2 w0 Rww0 H1

>_intro : ∀ {M : Model} {w : W M} {A B : Prop M} →  (∀ w' → F M (val A) w w' → M , w' ⊨ B)  →  M , w ⊨ A > B
>_intro {M} {w} {A} H w' H1 = H w' H1

>_elim : ∀ {M : Model} {w w' : W M} {A B : Prop M} →  M , w ⊨ A > B  → F M (val A) w w' →  M , w' ⊨ B
>_elim {M} {w}{w'} {A} H H1 = H w' H1

all_intro : ∀ {M : Model} {w : W M} {P : D M → Prop M} → (∀ d → M , w ⊨ P d)  →  M , w ⊨ ∀ᵐ[ P ]
all_intro {M}{w}{P} H d = H d

all_elim :  ∀ {M : Model} {w : W M} {P : D M → Prop M} (d :  D M) →  M , w ⊨ ∀ᵐ[ P ] → M , w ⊨ P d
all_elim = λ d H → H d

ex_intro :  ∀ {M : Model} {w : W M} {P : D M → Prop M} (d :  D M) →  M , w ⊨ P d → M , w ⊨ ∃ᵐ[ P ]
ex_intro {M} {w} {P} d H =  d , H

ex_elim : ∀ {M : Model} {w w' : W M} {P : D M → Prop M} {C : Prop M} → M , w ⊨ ∃ᵐ[ P ] → (∀ d → M , w ⊨ P d →  M , w' ⊨ C) → M , w' ⊨ C
ex_elim (d , Pd) H1 = H1 d Pd

app_elim : ∀ {M : Model} {w : W M} {P : D M → Prop M} {a : W M → D M} → M , w ⊨ P ∙ a → M , w ⊨ P (a w)
app_elim x = x

app_intro : ∀ {M : Model} {w : W M} {P : D M → Prop M} {a : W M → D M} → M , w ⊨ P (a w) → M , w ⊨ P ∙ a
app_intro x = x



Barcan_rev : ∀ {M : Model} {w : W M} {P : D M → Prop M} → (M , w ⊨ □ ∀ᵐ[ P ]) → (M , w ⊨ ∀ᵐ[ (λ d → □ (P d)) ]) 
Barcan_rev {M} {w} {P} H d w' Rww' = Goal where

 L1 : M , w' ⊨  ∀ᵐ[ P ]
 L1 = box_elim {M = M} H Rww'

 L2 : M , w' ⊨ P d
 L2 = all_elim {P = P} d L1

 Goal = L2

{- Фиттинг и Мендельсон, с 311., упр 14.2.1 -}
diam_lam_two : ∀ {M : Model} {w : W M} {P : D M → Prop M} {a : W M → D M} → M , w ⊨ ∀ᵐ[(λ d → ◇ (P d))] → M , w ⊨ ◇ (P (a w))
diam_lam_two {M} {w} {P} {a} H = H (a w)

diam_lam_one : ¬ ∀ {M : Model} {w : W M} {P : D M → Prop M} {a : W M → D M} → M , w ⊨ ◇ (P ∙ a) → M , w ⊨ ◇ (P (a w))

diam_lam_one H = Proof where

 R_Countermodel : Worlds-2 → Worlds-2 → Set₀
 R_Countermodel world-one world-two = ⊤
 R_Countermodel _ _ = ⊥

 Countermodel : Model
 Countermodel = record
    { W = Worlds-2
    ; witness-w = world-one
    ; D = Worlds-2
    ; witness-d = world-two
    ; R = R_Countermodel
    ; F = λ _ _ _ → ⊥
    }

 a : Worlds-2 → Worlds-2
 a w = w

 P : Worlds-2 → Prop Countermodel
 P world-one = record {val = λ _  → ⊥}
 P world-two = record {val = λ _  → ⊤ }

 Antecedent :  Countermodel , world-one ⊨ ◇ (P ∙ a)
 Antecedent = world-two , (tt , tt)

 Consequent :  Countermodel , world-one ⊨ ~ ◇ P (a world-one)
 Consequent (w' , R , Pa) =  Pa

 Proof = Consequent (H {Countermodel} {world-one} {P} {a} Antecedent)


{- Теперь пробуем логику более высокого порядка. Высшепорядковые модальные кванторы можно определить,
но в предикативной Agda это весьма большая работа. Зато все еще можно использовать дефолтные Пи- и Сигма-типы
для формулировки теорем высшего порядка. Что сейчас и сделаем -}

HOL_test : ∀ {M : Model} {w : W M} → Σ (D M → Prop M) (λ P → Σ (D M) (λ d → M , w ⊨ P d))
HOL_test {M} {w} = (λ d → (d =ᵐ witness-d M)) , ( witness-d M) , refl


-- Barcan : ∀ (M : Model) (w : W M) (P : D M → Prop M) → (M , w ⊨ ∀ᵐ[ (λ d → □ (P d)) ]) → (M , w ⊨ □ ∀ᵐ[ P ])
-- Barcan M w P H w' R d = Goal where

-- w - действительный мир
my-theorem : ∀ (M : Model) (w : W M) (Math : D M → Prop M) (Poet : D M → Prop M)
  (A : D M → Prop M) (P : D M → Prop M) (U : Universal M) → LEM →
  (Alice : D M) →
  -- любой поет является необходимо поэтичным и не необходимо аналитичным
  (M , w ⊨ ∀ᵐ[ (λ d → (□ (Poet d ⇒ P d)) ∧ (~ □ (Poet d ⇒ A d)))]) →
  -- любой математик является необходимо аналитичным и не необходимо поэтичным
  (M , w ⊨ ∀ᵐ[ (λ d → (□ (Math d ⇒ A d)) ∧ (~ □ (Math d ⇒ P d)))]) →
  (M , w ⊨ Math Alice ∧ Poet Alice) →
  ⊥

my-theorem = λ M w Math Poet A P U (lem : LEM) Alice Poet_prop Math_prop
  (Alice_M_P : M , w ⊨ Math Alice ∧ Poet Alice) →
  let
    -- устраняем кванторы всеобщности, подставляя Alice
    Alice_math : M , w ⊨ (□ (Math Alice ⇒ A Alice) ∧ ~ □ (Math Alice ⇒ P Alice))
    Alice_math = all_elim {P = (λ d → □ (Math d ⇒ A d) ∧ ~ □ (Math d ⇒ P d))} Alice Math_prop

    Alice_poet : M , w ⊨ (□ (Poet Alice ⇒ P Alice) ∧ ~ □ (Poet Alice ⇒ A Alice))
    Alice_poet = all_elim {P = (λ d → □ (Poet d ⇒ P d) ∧ ~ □ (Poet d ⇒ A d))} Alice Poet_prop

    -- Разбиение 1-й конъюнкции
    boxMath_Analitical : M , w ⊨ □ (Math Alice ⇒ A Alice)
    boxMath_Analitical = and_elim1 {A = □ (Math Alice ⇒ A Alice)} {B = ~ □ (Math Alice ⇒ P Alice)} Alice_math

    nboxMath_Poetical : M , w ⊨ ~ □ (Math Alice ⇒ P Alice)
    nboxMath_Poetical = and_elim2 {A = □ (Math Alice ⇒ A Alice)} {B = ~ □ (Math Alice ⇒ P Alice)} Alice_math

    -- Разбиение 2-й конъюнкции
    boxPoet_Poetical : M , w ⊨ (□ (Poet Alice ⇒ P Alice))
    boxPoet_Poetical = and_elim1 {A = □ (Poet Alice ⇒ P Alice)} {B = ~ □ (Poet Alice ⇒ A Alice)} Alice_poet

    nboxPoet_Analytical : M , w ⊨ ~ □ (Poet Alice ⇒ A Alice)
    nboxPoet_Analytical = and_elim2 {A = □ (Poet Alice ⇒ P Alice)} {B = ~ □ (Poet Alice ⇒ A Alice)} Alice_poet

    -- разбиение 3-й конъюнкции: Alice математик и поэт
    MA : (M , w ⊨ Math Alice)
    MA = and_elim1 {A = Math Alice} {B = Poet Alice} Alice_M_P

    PA : (M , w ⊨ Poet Alice)
    PA = and_elim2 {A = Math Alice} {B = Poet Alice} Alice_M_P

    Rww : R M w w
    Rww = U w w
    boxMath_Analitical1 : M , w ⊨ Math Alice ⇒ A Alice
    boxMath_Analitical1 = box_elim {M = M} boxMath_Analitical Rww
    nboxPoet_Analytical2 : M , w ⊨ ◇ ~ (Poet Alice ⇒ A Alice)
-- neg_box : ∀ {M : Model} {w : W M} {A : Prop M} → (lem : LEM) →  M , w ⊨ ~ □ A  → M , w ⊨ ◇ ~ A    
    nboxPoet_Analytical2 = neg_box {M = M} lem nboxPoet_Analytical
    w' , Rww' , nPoet_A = nboxPoet_Analytical2
    Math_analitical : M , w' ⊨ Math Alice ⇒ A Alice
    Math_analitical = box_elim {M = M} boxMath_Analitical Rww'
    nboxMath_Poetical1 : M , w ⊨ ◇ ~ (Math Alice ⇒ P Alice)
    nboxMath_Poetical1 = neg_box {M = M} lem nboxMath_Poetical
    w2 , Rww2 , nMath_P = nboxMath_Poetical1
--    Poet-poetical : M , w' ⊨ Math Alice ⇒ A Alice
--    Poet-poetical = box_elim {M = M} boxPoet_Poetical Rww2
--    nboxMath_Poetical1 : M , w ⊨ Math Alice ⇒ P Alice
--    nboxMath_Poetical1 = box_elim {M = M} nboxMath_Poetical Rww
  in
    {!!}
