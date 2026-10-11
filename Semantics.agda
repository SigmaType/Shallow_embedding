{-# OPTIONS --safe -- #-}

module Semantics where

record Model : Set₁ where
  field
    W : Set₀
    witness-w : W

    D : Set₀
    witness-d : D

    R : W → W → Set₀
    F : (W → Set₀) → W → W → Set₀

 {- Нашей базовой логикой будет являться минимальная экстенсиональная кондициональная логика
 с K-отношением достижимости для модальных операторов -}
