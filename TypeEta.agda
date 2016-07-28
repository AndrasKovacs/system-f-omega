
module SystemFOmega.TypeEta where

open import SystemFOmega.Type
open import SystemFOmega.TypeProofs



-- Goal: T.inst (T.η vz) (T.ren (keep top) B) ≡ B
-- ————————————————————————————————————————————————————————————
-- sp : Sp Δ .A (∀' B)
-- v  : .A ∈ Δ
-- .A : Ty .Γ ⋆
-- Δ  : Con .Γ
-- B  : Ty (.Γ ▷ A) ⋆
-- A  : Kind
-- .Γ : T.Con

