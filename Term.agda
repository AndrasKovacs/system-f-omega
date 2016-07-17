{-# OPTIONS --without-K #-}

module SystemFOmega.Term where

open import SystemFOmega.Type

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product

--------------------------------------------------------------------------------

data Conₜ : Conₖ → Set where
  ε    : Conₜ ε
  _,ₜ_ : ∀ {Γ} → Conₜ Γ → NfTy Γ ⋆ → Conₜ Γ
  _,ₖ_ : ∀ {Γ} → Conₜ Γ → (A : Kind) → Conₜ (Γ , A)
infixl 5 _,ₜ_ _,ₖ_

data _∈ₜ_ : ∀ {Γ} → NfTy Γ ⋆ → Conₜ Γ → Set where
  vz   : ∀ {Γ}{Δ : Conₜ Γ}{A}   → A ∈ₜ (Δ ,ₜ A)
  vsₜ_ : ∀ {Γ}{Δ : Conₜ Γ}{A B} → A ∈ₜ Δ → A ∈ₜ (Δ ,ₜ B)
  vsₖ_ : ∀ {Γ}{Δ : Conₜ Γ}{A B} → A ∈ₜ Δ → ren-NfTy top A ∈ₜ (Δ ,ₖ B)

data Tm {Γ} (Δ : Conₜ Γ) : NfTy Γ ⋆ → Set where
  var  : ∀ {A} → A ∈ₜ Δ → Tm Δ A
  λ'   : ∀ A {B} → Tm (Δ ,ₜ A) B → Tm Δ (A ⇒ B)
  _∙_  : ∀ {A B} → Tm Δ (A ⇒ B) → Tm Δ A → Tm Δ B
  Λ    : ∀ A {B} → Tm (Δ ,ₖ A) B → Tm Δ (∀' A B)
  _∙ₜ_ : ∀ {A B} → Tm Δ (∀' A B) → (t : NfTy Γ A) → Tm Δ (instTy t B)
infixl 6 _∙ₜ_

mutual
  data NfTm {Γ} (Δ : Conₜ Γ) : NfTy Γ ⋆ → Set where
    λ'   : ∀ A {B} → NfTm (Δ ,ₜ A) B → NfTm Δ (A ⇒ B)
    Λ    : ∀ A {B} → NfTm (Δ ,ₖ A) B → NfTm Δ (∀' A B)
    ne   : ∀ {n} → NeTm Δ (ne n) → NfTm Δ (ne n)

  data NeTm {Γ} (Δ : Conₜ Γ) : NfTy Γ ⋆ → Set where
    _,_ : ∀ {A B} → A ∈ₜ Δ → SpTm Δ A B → NeTm Δ B

  data SpTm {Γ} (Δ : Conₜ Γ) : NfTy Γ ⋆ → NfTy Γ ⋆ → Set where
    ε    : ∀ {A} → SpTm Δ A A
    _∷ₜ_ : ∀ {A B C} → NfTm Δ A → SpTm Δ B C → SpTm Δ (A ⇒ B) C
    _∷ₖ_ : ∀ {A B C} → (t : NfTy Γ A) → SpTm Δ (instTy t B) C → SpTm Δ (∀' A B) C
  infixr 5 _∷ₜ_ _∷ₖ_

-- Renaming
--------------------------------------------------------------------------------

data _⊆[_]_ : ∀ {Γ Γ'} → Conₜ Γ → Γ ⊆ Γ' → Conₜ Γ' → Set where
  stop  : ε ⊆[ stop ] ε
  addₖ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ add s  ] (Ξ ,ₖ A)
  addₜ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ s      ] (Ξ ,ₜ A)
  keepₖ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ,ₖ A) ⊆[ keep s ] (Ξ ,ₖ A)
  keepₜ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ,ₜ A) ⊆[ s      ] (Ξ ,ₜ ren-NfTy s A)

⊆-of : ∀ {Γ Γ' Δ Ξ}{s : Γ ⊆ Γ'} → Δ ⊆[ s ] Ξ → Γ ⊆ Γ'
⊆-of {s = s} _ = s

idᵗ : ∀ {Γ}{Δ : Conₜ Γ} → Δ ⊆[ idᵏ ] Δ
idᵗ {_}{ε}      = stop
idᵗ {_}{Δ ,ₜ x} = subst (λ y → (Δ ,ₜ x) ⊆[ idᵏ ] (Δ ,ₜ y)) (ren-NfTy-id x) (keepₜ idᵗ)
idᵗ {_}{Δ ,ₖ A} = keepₖ idᵗ

topᵗ : ∀ {Γ}{Δ : Conₜ Γ} {A} → Δ ⊆[ idᵏ ] (Δ ,ₜ A)
topᵗ = addₜ idᵗ

topᵏ : ∀ {A Γ}{Δ : Conₜ Γ} → Δ ⊆[ top ] (Δ ,ₖ A)
topᵏ = addₖ idᵗ

ren-∈ₜ : ∀ {Γ Γ' Δ Ξ A}{ks : Γ ⊆ Γ'} → Δ ⊆[ ks ] Ξ → A ∈ₜ Δ → ren-NfTy ks A ∈ₜ Ξ
ren-∈ₜ stop ()
ren-∈ₜ (addₖ s)  v       = subst (_∈ₜ _) (top-add _ _ _) (vsₖ (ren-∈ₜ s v))
ren-∈ₜ (addₜ s)  v       = vsₜ (ren-∈ₜ s v)
ren-∈ₜ (keepₖ s) (vsₖ v) = subst (_∈ₜ _) (keep-top _ _ _) (vsₖ (ren-∈ₜ s v))
ren-∈ₜ (keepₜ s) vz      = vz
ren-∈ₜ (keepₜ s) (vsₜ v) = vsₜ ren-∈ₜ s v

mutual
  ren-NfTm : ∀ {Γ Γ' Δ Ξ A}{s : Γ ⊆ Γ'} → Δ ⊆[ s ] Ξ → NfTm Δ A → NfTm Ξ (ren-NfTy s A)
  ren-NfTm s (λ' _ t) = λ' _ (ren-NfTm (keepₜ s) t)
  ren-NfTm s (Λ  _ t) = Λ  _ (ren-NfTm (keepₖ s) t)
  ren-NfTm s (ne {_ , _} (v , sp)) = ne (ren-∈ₜ s v , ren-SpTm s sp)

  ren-SpTm :
    ∀ {Γ Γ' Δ Ξ A B}{s : Γ ⊆ Γ'} → Δ ⊆[ s ] Ξ → SpTm Δ A B → SpTm Ξ (ren-NfTy s A) (ren-NfTy s B)
  ren-SpTm s ε         = ε
  ren-SpTm s (x ∷ₜ sp) = ren-NfTm s x        ∷ₜ ren-SpTm s sp
  ren-SpTm s (t ∷ₖ sp) = ren-NfTy (⊆-of s) t ∷ₖ {!ren-SpTm s sp!} -- TODO: subst-wk commute

ren-NfTm' : ∀ {Γ Δ Ξ A} → Δ ⊆[ idᵏ ] Ξ → NfTm {Γ} Δ A → NfTm Ξ A
ren-NfTm' s t = subst (NfTm _) (ren-NfTy-id _) (ren-NfTm s t)

ren-SpTm' : ∀ {Γ Δ Ξ A B} → Δ ⊆[ idᵏ ] Ξ → SpTm {Γ} Δ A B → SpTm Ξ A B
ren-SpTm' s t = subst₂ (SpTm _) (ren-NfTy-id _) (ren-NfTy-id _) (ren-SpTm s t)

data Ixₜ : ∀ {Γ} → Ixₖ Γ → Conₜ Γ → Set where
  iz   : ∀ {Γ Δ}     → Ixₜ {Γ} iz Δ
  isₖ_ : ∀ {Γ Δ A i} → Ixₜ {Γ} i Δ → Ixₜ (is i) (Δ ,ₖ A)
  isₜ_ : ∀ {Γ Δ A i} → Ixₜ {Γ} i Δ → Ixₜ i (Δ ,ₜ A)

Ixₖ-of : ∀ {Γ Δ i} → Ixₜ {Γ} i Δ → Ixₖ Γ
Ixₖ-of {i = i} _ = i

insₖ : ∀ {Γ Δ i} A → Ixₜ {Γ} i Δ → Conₜ (ins i A)
insₖ {Δ = Δ}      A iz      = Δ ,ₖ A
insₖ {Δ = Δ ,ₖ B} A (isₖ i) = insₖ A i ,ₖ B
insₖ {Δ = Δ ,ₜ B} A (isₜ i) = insₖ A i ,ₜ ren-NfTy (ins-⊆ (Ixₖ-of i) A) B

insₜ : ∀ {Γ Δ i} → NfTy (drop {Γ} i) ⋆ → Ixₜ i Δ → Conₜ Γ
insₜ {Δ = Δ}      A iz      = Δ ,ₜ A
insₜ {Δ = Δ ,ₖ B} A (isₖ i) = insₜ A i ,ₖ B
insₜ {Δ = Δ ,ₜ B} A (isₜ i) = insₜ A i ,ₜ B

-- Normalization
--------------------------------------------------------------------------------

snocSpTmₜ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (B ⇒ C) → NfTm Δ B → SpTm Δ A C
snocSpTmₜ ε         t = t ∷ₜ ε
snocSpTmₜ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₜ sp t
snocSpTmₜ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₜ sp t

snocSpTmₖ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (∀' B C) → (t : NfTy Γ B) → SpTm Δ A (instTy t C)
snocSpTmₖ ε         t = t ∷ₖ ε
snocSpTmₖ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₖ sp t
snocSpTmₖ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₖ sp t

-- Proof
inst-top : ∀ {Γ A B}(t' : NfTy Γ B)(t : NfTy Γ A) → instTy t' (ren-NfTy top t) ≡ t
inst-top = {!!}
-- Proof

mutual
  η-Tm : ∀ {Γ Δ A} → A ∈ₜ Δ → NfTm {Γ} Δ A
  η-Tm v = η-NeTm (v , ε)
  
  η-NeTm : ∀ {Γ Δ A} → NeTm {Γ} Δ A → NfTm Δ A
  η-NeTm {A = A ⇒ B}  (v , sp) = λ' A (η-NeTm (vsₜ v , snocSpTmₜ (ren-SpTm' topᵗ sp) (η-Tm vz)))
  η-NeTm {Γ}{Δ}{A = ∀' A B} (_,_ {C} v sp) = Λ A {!!}
    -- Λ A (η-NeTm (vsₖ v ,    -- where does the renaming come from??
    --   subst (SpTm (Δ ,ₖ A) (ren-NfTy top C)) (inst-top (η-Ty vz) B)
    --   (snocSpTmₖ {_}{Δ ,ₖ A}{ren-NfTy top C}{A}{ren-NfTy top B}
    --   {!ren-SpTm (topᵏ{A}) sp !} -- Proof!
    --   (η-Ty vz)) ))
  η-NeTm {A = ne nt}  n = ne n

