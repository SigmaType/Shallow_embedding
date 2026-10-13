{-# OPTIONS --safe -- #-}
module Propositional where

open import Data.Product
-- Дано:
-- ⊢ A : Set
--
-- Построй:
-- A : Set, x : A ⊢ x : A

-- Если делать всё явно
I : (A : Set) → (x : A) → A
I = λ (A : Set) (x : A) → x

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

K : {A B : Set} -> A -> B -> A
K {A} {B} = λ (a : A) (_ : B) → a

S : {A B C : Set} → (A → B → C) → (A → B) → (A → C)
S {A} {B} {C} = λ (f : A → B → C) (g : A → B) (a : A) → f a (g a)

B : {A B C : Set} → (B → C) → (A → B) → A → C
B {A} {B} {C} = λ (f : B → C) (g : A → B) (a : A) → f (g a)

C : {A B C : Set} → (A → B → C) → B → A → C
C {A} {B} {C} = λ (f : A → B → C) (b : B) (a : A) → f a b

W : {A B : Set} → (A → A → B) → A → B
W {A} {B} = λ (f : A → A → B) (a : A) → f a a

conj-comm : {A B : Set} → A × B → B × A
conj-comm {A} {B} = λ (conj : A × B) → proj₂ conj , proj₁ conj

disj-comm : {A B : Set} → A ⊎ B → B ⊎ A
disj-comm (inj₁ x) = inj₂ x
disj-comm (inj₂ y) = inj₁ y

conj-assoc : {A B C : Set} → A × (B × C) → (A × B) × C
conj-assoc {A} {B} {C} (a , (b , c)) = (a , b) , c

disj-assoc : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
disj-assoc {A} {B} {C} (inj₁ a) = inj₁ (inj₁ a)
disj-assoc {A} {B} {C} (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
disj-assoc {A} {B} {C} (inj₂ (inj₂ c)) = inj₂ c

contra : {A : Set} → ¬ (A × ¬ A)
contra {A} = λ (conj : A × ¬ A) →
  let
    a : A
    a = proj₁ conj
    na : A → ⊥
    na = proj₂ conj
  in
    na a

trans : {A B C : Set} → (A → B) → (B → C) → (A → C)
trans {A} {B} {C} = λ (f : A → B) (g : B → C) (a : A) → g (f a)

conj-distrib1 : {A Q R : Set} → (A × (Q ⊎ R)) → (A × Q) ⊎ (A × R)
conj-distrib1 {A} {Q} {R} = λ (conj : A × (Q ⊎ R)) →
  let
    a : A
    a = proj₁ conj
    q_or_r : Q ⊎ R
    q_or_r = proj₂ conj
  in
    case-⊎
    (λ (q : Q) →
      inj₁ (a , q))
    (λ (r : R) →
      inj₂ (a , r))
    q_or_r

conj-distrib2 : {P Q R : Set} → (P × Q) ⊎ (P × R) → (P × (Q ⊎ R))
conj-distrib2 {P} {Q} {R} (inj₁ (p , q)) = p , (inj₁ q)
conj-distrib2 {P} {Q} {R} (inj₂ (p , r)) = p , (inj₂ r)

disj-distrib1 : {A B C : Set} → (A ⊎ (B × C)) → (A ⊎ B) × (A ⊎ C)
disj-distrib1 {A} {B} {C} (inj₁ a) = (inj₁ a) , (inj₁ a)
disj-distrib1 {A} {B} {C} (inj₂ (b , c)) = (inj₂ b) , (inj₂ c)

disj-distrib2 : {A B C : Set} → (A ⊎ B) × (A ⊎ C) → (A ⊎ (B × C))
disj-distrib2 {A} {B} {C} (inj₁ a , _) = inj₁ a
disj-distrib2 {A} {B} {C} (inj₂ _ , inj₁ a) = inj₁ a
disj-distrib2 {A} {B} {C} (inj₂ b , inj₂ c) = inj₂ (b , c)

dbl-neg-intro : {A : Set} → A → ¬ (¬ A)
dbl-neg-intro {A} = λ (a : A) (neg_a : A → ⊥) → neg_a a

LEM : Set₁
LEM = ∀ (A : Set) → A ⊎ ¬ A

DNE : Set₁
DNE = ∀ (A : Set) → ¬ ¬ A → A

dbl-neg-elim : LEM → DNE
dbl-neg-elim = λ (lem : LEM) (A : Set) (nna : ¬ ¬ A) →
  case-⊎
  (λ (a : A) →
    a)
  (λ (na : ¬ A) →
    ⊥-elim (nna na))
  (lem A)

modus-tollens : {A B : Set} → (A → B) → ¬ B → ¬ A
modus-tollens {A} {B} = λ (A_B : A → B) (nb : ¬ B) (a : A) → nb (A_B a)

MTPl : {A B : Set} → A ⊎ B → ¬ A → B
MTPl {A} {B} (inj₁ a) (na) = ⊥-elim (na a)
MTPl {A} {B} (inj₂ b) (na) = b

MTPr : {A B : Set} → A ⊎ B → ¬ B → A
MTPr {A} {B} (inj₁ a) _ = a
MTPr {A} {B} (inj₂ b) (nb) = ⊥-elim (nb b)

contrapos-rev : {A B : Set} → LEM → (¬ B → ¬ A) → (A → B)
contrapos-rev {A} {B} = λ (lem : LEM) (f : ¬ B → ¬ A) (a : A) →
  case-⊎
  (λ (b : B) →
    b)
  (λ (nb : ¬ B) →
    ⊥-elim ((f nb) a))
  (lem B)

impl-disj : {A B : Set} → LEM → (A → B) → (¬ A ⊎ B)
impl-disj {A} {B} = λ (lem : LEM) (f : A → B) →
  let
    disjA : A ⊎ ¬ A
    disjA = lem A
    disjB : B ⊎ ¬ B
    disjB = lem B
  in
    case-⊎
    (λ (a : A) →
      case-⊎
      (λ (b : B) →
        inj₂ b)
      (λ (nb : ¬ B) →
        let
          b : B
          b = f a
        in
          ⊥-elim (nb b)
      )
      disjB)
    (λ (na : ¬ A) →
      inj₁ na)
    disjA

nimpl-conj : {A B : Set} → (lem : LEM) → ¬ (A → B) → A × ¬ B
nimpl-conj {A} {B} = λ (lem : LEM) (f : ¬ (A → B)) →
  let
    disjA : A ⊎ ¬ A
    disjA = lem A
    disjB : B ⊎ ¬ B
    disjB = lem B
  in
    case-⊎
      (λ (b : B) →
        let
          g : A → B
          g = λ (_ : A) → b
        in
          ⊥-elim (f g)
      )
      (λ (nb : ¬ B) →
        case-⊎
        (λ (a : A) →
          a , nb
        )
        (λ (na : ¬ A) →
          let
            H1 : (¬ B → ¬ A) → (¬ ¬ A → ¬ ¬ B)
            H1 = modus-tollens {¬ B} {¬ A}
            H2 : ¬ B → ¬ A
            H2 = λ (_ : ¬ B) → na
            H3 : ¬ ¬ A → ¬ ¬ B
            H3 = H1 H2
            H4 : A → ¬ ¬ A
            H4 = dbl-neg-intro {A}
            H5 : A → ¬ ¬ B
            H5 = trans H4 H3
            H6 : ¬ ¬ B → B
            H6 = dbl-neg-elim lem B
            H7 : A → B
            H7 = trans H5 H6
          in
            ⊥-elim (f H7)
        )
        disjA
      )
    disjB


de-morgan-ndisj-conj : {A B : Set} → ¬ ( A ⊎ B) → ¬ A × ¬ B
de-morgan-ndisj-conj {A} {B} = λ (n_disj : ¬ ( A ⊎ B)) →
  let
    na : ¬ A
    na = λ (a : A) → n_disj (inj₁ a)
    nb : ¬ B
    nb = λ (b : B) → n_disj (inj₂ b)
  in
    na , nb

de-morgan-conj-ndisj : {A B : Set} → ¬ A × ¬ B → ¬ (A ⊎ B)
de-morgan-conj-ndisj {A} {B} (na , _) (inj₁ a) = na a
de-morgan-conj-ndisj {A} {B} (_ , nb) (inj₂ b) = nb b

de-morgan-nconj-disj : {A B : Set} → LEM → ¬ (A × B) → ¬ A ⊎ ¬ B
de-morgan-nconj-disj {A} {B} = λ (lem : LEM) (nconj : ¬ (A × B)) →
  case-⊎
  (λ (a : A) →
    let
      nb : ¬ B
      nb = λ (b : B) → nconj (a , b)
    in
      inj₂ nb)
  (λ (na : ¬ A) →
    inj₁ na)
  (lem A)

de-morgan-disj-nconj : {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
de-morgan-disj-nconj {A} {B} (inj₁ na) (a , _) = na a
de-morgan-disj-nconj {A} {B} (inj₂ nb) (_ , b) = nb b

neg-neg-lem : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
neg-neg-lem {A} = λ (contra : ¬ (A ⊎ ¬ A)) →
  let
    conj : ¬ A × ¬ ¬ A
    conj = de-morgan-ndisj-conj contra
    nA : ¬ A
    nA = proj₁ conj
    nnA : ¬ ¬ A
    nnA = proj₂ conj
  in
    nnA nA

dne-lem : DNE → LEM
dne-lem = λ (dbl-neg-elim : DNE) (A : Set) →
  let
    nn-disj : ¬ ¬ (A ⊎ ¬ A)
    nn-disj = neg-neg-lem
    elim : ¬ (¬ (A ⊎ ¬ A)) → (A ⊎ ¬ A)
    elim = dbl-neg-elim (A ⊎ ¬ A)
    goal : A ⊎ ¬ A
    goal = elim nn-disj
  in
    goal

Peirce : Set₁
Peirce = ∀ (P Q : Set) → ((P → Q) → P) → P

lem-peirce : LEM → Peirce
lem-peirce = λ (lem : LEM) (P Q : Set) (impl : (P → Q) → P) →
    case-⊎
    (λ (p : P) →
      p)
    (λ (np : ¬ P) →
      let
        f : P → Q
        f = λ (p : P) → ⊥-elim (np p)
      in
        impl f)
    (lem P)

peirce-dne : Peirce → DNE
peirce-dne = λ (pierce : Peirce) (A : Set) (nna : ¬ ¬ A) →
  let
    clavius : (¬ A → A) → A
    clavius = pierce A ⊥
    na_impl_a : ¬ A → A
    na_impl_a = λ (na : ¬ A) → ⊥-elim (nna na)
  in
    clavius na_impl_a

peirce-lem : Peirce → LEM
peirce-lem = λ (pierce : Peirce) → dne-lem (peirce-dne pierce)

T1 : {A B C D : Set} → ((A ⊎ B) → (C × D)) → ¬ C → ¬ B
T1 {A} {B} {C} {D} = λ (impl : (A ⊎ B) → (C × D)) (nc : ¬ C) (b : B) →
  let
    a_or_b : A ⊎ B
    a_or_b = inj₂ b
    c_and_d : C × D
    c_and_d = impl a_or_b
    c : C
    c = proj₁ c_and_d
  in
    nc c

T2 : {A B C : Set} → (lem : LEM) → ((A × ¬ B) → ¬ C) → (A × C) → B
T2 {A} {B} {C} = λ (lem : LEM) (impl : (A × ¬ B) → ¬ C) (conj : (A × C)) →
  let
    a : A
    a = proj₁ conj
    c : C
    c = proj₂ conj
    nnC : ¬ ¬ C
    nnC = dbl-neg-intro c
    n_conj : ¬ (A × ¬ B)
    n_conj = modus-tollens impl nnC
    disj : ¬ A ⊎ ¬ ¬ B
    disj = de-morgan-nconj-disj lem n_conj
  in
    case-⊎
    (λ (na : ¬ A) →
      ⊥-elim (na a))
    (λ (nnb : ¬ ¬ B) →
      dbl-neg-elim lem B nnb)
    disj

T3 : {A B C : Set} → (A × B → C) → (A × ¬ C) → ¬ B
T3 {A} {B} {C} = λ (H1 : A × B → C) (a_nc : A × ¬ C) (b : B) →
  let
    a : A
    a = proj₁ a_nc
    nc : ¬ C
    nc = proj₂ a_nc
    a_b : A × B
    a_b = a , b
    c : C
    c = H1 a_b
  in
    nc c

T4 : {A B C : Set} → (A ⊎ C → ¬ B) → (B → ¬ A)
T4 {A} {B} {C} = λ (H : (A ⊎ C → ¬ B)) (b : B) (a : A) →
  let
    nnB : ¬ ¬ B
    nnB = dbl-neg-intro b
    ndisj : ¬ (A ⊎ C)
    ndisj = modus-tollens H nnB
    conj : ¬ A × ¬ C
    conj = de-morgan-ndisj-conj ndisj
    nA : ¬ A
    nA = proj₁ conj
  in
    ⊥-elim (nA a)

T5 : {A B : Set} → (A → B) → ¬ B → (¬ A × ¬ B)
T5 {A} {B} = λ (f : A → B) (nB : ¬ B) →
  let
    nA : ¬ A
    nA = modus-tollens f nB
  in
    nA , nB

T6 : {A B C : Set} → ((A × B) → C) → (A × ¬ C) → ¬ B
T6 {A} {B} {C} = λ (f : (A × B) → C) (conj : A × ¬ C) (b : B) →
  let
    a : A
    a = proj₁ conj
    nC : ¬ C
    nC = proj₂ conj
    H1 : A × B
    H1 = a , b
    c : C
    c = f H1
  in
    nC c

T7 : {A B C : Set} → ((A → B) × (B → C)) → ¬ C → ¬ A
T7 {A} {B} {C} = λ (conj : (A → B) × (B → C)) (nC : ¬ C) (a : A) →
  let
    a_b : A → B
    a_b = proj₁ conj
    b_c : B → C
    b_c = proj₂ conj
    b : B
    b = a_b a
    c : C
    c = b_c b
  in
    nC c

T8 : {A B C : Set} → (A → B) × (A → C) → (¬ B ⊎ ¬ C) → ¬ A
T8 {A} {B} {C} = λ (a_b , a_c) (disj : ¬ B ⊎ ¬ C) (a : A) →
  case-⊎
  (λ (nb : ¬ B) →
    nb (a_b a))
  (λ (nc : ¬ C) →
    nc (a_c a))
  disj

n∃-∀n : {A : Set} → (P : A → Set) → ¬ Σ A P → ∀ (x : A) → ¬ (P x)
n∃-∀n {A} = λ (P : A → Set) (nEx : ¬ Σ A P) →
  λ (x : A) (Px : P x) → nEx (x , Px)

∀-DNE : {A : Set} → {P : A → Set} → DNE → (∀ (x : A) → ¬ ¬ (P x)) → (∀ (x : A) → P x)
∀-DNE {A} {P} = λ (dne : DNE) (f : ∀ (x : A) → ¬ ¬ (P x)) →
  λ (x : A) → dne (P x) (f x)

not-fall-exists : {A : Set} → {P : A → Set} → (lem : LEM) → (¬ ∀ (x : A) → P x) → Σ A (λ x → ¬ P x)
not-fall-exists {A} {P} = λ (lem : LEM) (nfa_Px : ¬ ∀ (x : A) → P x) →
  let
    dne : DNE
    dne = dbl-neg-elim lem
  in
    dne (Σ A (λ x → ¬ P x)) (λ (ngoal : ¬ Σ A (λ x → ¬ P x)) →
    let
      fa_nnPx : ∀ (x : A) → ¬ (¬ P x)
      fa_nnPx = n∃-∀n (λ x → ¬ P x) ngoal
      fa_Px : ∀ (x : A) → P x
      fa_Px = ∀-DNE dne fa_nnPx
    in
      nfa_Px fa_Px)
