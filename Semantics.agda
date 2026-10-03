{-# OPTIONS --safe -- #-}

module Semantics where

record Model : Set₁ where
  field
    𝐖 : Set₀
    witness-w : 𝐖

    𝐃 : Set₀
    witness-d : 𝐃

    𝐑 : 𝐖 → 𝐖 → Set₀
    𝐅 : (𝐖 → Set₀) → 𝐖 → 𝐖 → Set₀

 {- Нашей базовой логикой будет являться минимальная экстенсиональная кондициональная логика
 с K-отношением достижимости для моадльных операторов -}
