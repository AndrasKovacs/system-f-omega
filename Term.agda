{-# OPTIONS --without-K #-}

module SystemFOmega.Term where

open import SystemFOmega.Type
  hiding (Con; _∈_; ren-∈; id; Ix; Ne; η-Ne; η; Sp; ren; renSp; sub; drop; drop-⊆)
import SystemFOmega.Type as T

open import Relation.Binary.PropositionalEquality
open import Data.Product

import Function as F

--------------------------------------------------------------------------------

data Con : T.Con → Set where
  ε    : Con ε
  _▷ₜ_ : ∀ {Γ} → Con Γ → Ty Γ ⋆ → Con Γ
  _▷ₖ_ : ∀ {Γ} → Con Γ → (A : Kind) → Con (Γ ▷ A)
infixl 5 _▷ₜ_ _▷ₖ_

data _∈_ : ∀ {Γ} → Ty Γ ⋆ → Con Γ → Set where
  vz   : ∀ {Γ}{Δ : Con Γ}{A}   → A ∈ (Δ ▷ₜ A)
  vsₜ_ : ∀ {Γ}{Δ : Con Γ}{A B} → A ∈ Δ → A ∈ (Δ ▷ₜ B)
  vsₖ_ : ∀ {Γ}{Δ : Con Γ}{A B} → A ∈ Δ → T.ren top A ∈ (Δ ▷ₖ B)

data Tm {Γ} (Δ : Con Γ) : Ty Γ ⋆ → Set where
  var  : ∀ {A} → A ∈ Δ → Tm Δ A
  ƛ_   : ∀ {A B} → Tm (Δ ▷ₜ A) B → Tm Δ (A ⇒ B)
  _∙_  : ∀ {A B} → Tm Δ (A ⇒ B) → Tm Δ A → Tm Δ B
  Λ_   : ∀ {A B} → Tm (Δ ▷ₖ A) B → Tm Δ (∀' B)
  _∙ₜ_ : ∀ {A B} → Tm Δ (∀' B) → (t : Ty Γ A) → Tm Δ (T.inst t B)
infixl 6 _∙ₜ_

mutual
  data Nf {Γ} (Δ : Con Γ) : Ty Γ ⋆ → Set where
    ƛ_   : ∀ {A B} → Nf (Δ ▷ₜ A) B → Nf Δ (A ⇒ B)
    Λ_   : ∀ {A B} → Nf (Δ ▷ₖ A) B → Nf Δ (∀' B)
    ne   : ∀ {n} → Ne Δ (ne n) → Nf Δ (ne n)

  data Ne {Γ} (Δ : Con Γ) : Ty Γ ⋆ → Set where
    _,_ : ∀ {A B} → A ∈ Δ → Sp Δ A B → Ne Δ B

  data Sp {Γ} (Δ : Con Γ) : Ty Γ ⋆ → Ty Γ ⋆ → Set where
    ε    : ∀ {A} → Sp Δ A A
    _∷ₜ_ : ∀ {A B C} → Nf Δ A → Sp Δ B C → Sp Δ (A ⇒ B) C
    _∷ₖ_ : ∀ {A B C} → (t : Ty Γ A) → Sp Δ (T.inst t B) C → Sp Δ (∀' B) C
  infixr 5 _∷ₜ_ _∷ₖ_

-- Renaming
--------------------------------------------------------------------------------

data _⊆[_]_ : ∀ {Γ Γ'} → Con Γ → Γ ⊆ Γ' → Con Γ' → Set where
  stop  : ε ⊆[ stop ] ε
  addₖ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ add s  ] (Ξ ▷ₖ A)
  addₜ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ s      ] (Ξ ▷ₜ A)
  keepₖ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ▷ₖ A) ⊆[ keep s ] (Ξ ▷ₖ A)
  keepₜ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ▷ₜ A) ⊆[ s      ] (Ξ ▷ₜ T.ren s A)

⊆-of : ∀ {Γ Γ' Δ Ξ}{o : Γ ⊆ Γ'} → Δ ⊆[ o ] Ξ → Γ ⊆ Γ'
⊆-of {o = o} _ = o

id : ∀ {Γ}{Δ : Con Γ} → Δ ⊆[ T.id ] Δ
id {_}{ε}      = stop
id {_}{Δ ▷ₜ t} = subst (λ y → (Δ ▷ₜ t) ⊆[ T.id ] (Δ ▷ₜ y)) (T.ren-id t) (keepₜ id)
id {_}{Δ ▷ₖ A} = keepₖ id

topᵗ : ∀ {Γ}{Δ : Con Γ} {A} → Δ ⊆[ T.id ] (Δ ▷ₜ A)
topᵗ = addₜ id

topᵏ : ∀ {A Γ}{Δ : Con Γ} → Δ ⊆[ top ] (Δ ▷ₖ A)
topᵏ = addₖ id

ren-∈ : ∀ {Γ Γ' Δ Ξ A}{o : Γ ⊆ Γ'} → Δ ⊆[ o ] Ξ → A ∈ Δ → T.ren o A ∈ Ξ
ren-∈ stop ()
ren-∈ (addₖ o)  v       = subst (_∈ _) (top-add _ _) (vsₖ (ren-∈ o v))
ren-∈ (addₜ o)  v       = vsₜ (ren-∈ o v)
ren-∈ (keepₖ o) (vsₖ v) = subst (_∈ _) (top-keep _ _) (vsₖ (ren-∈ o v))
ren-∈ (keepₜ o) vz      = vz
ren-∈ (keepₜ o) (vsₜ v) = vsₜ ren-∈ o v

mutual
  ren : ∀ {Γ Γ' Δ Ξ A}{o : Γ ⊆ Γ'} → Δ ⊆[ o ] Ξ → Nf Δ A → Nf Ξ (T.ren o A)
  ren o (ƛ t) = ƛ (ren (keepₜ o) t)
  ren o (Λ t) = Λ (ren (keepₖ o) t)
  ren o (ne {_ , _} (v , sp)) = ne (ren-∈ o v , renSp o sp)

  renSp : ∀ {Γ Γ' Δ Ξ A B}{o : Γ ⊆ Γ'} → Δ ⊆[ o ] Ξ → Sp Δ A B → Sp Ξ (T.ren o A) (T.ren o B)
  renSp o ε         = ε
  renSp o (x ∷ₜ sp) = ren o x ∷ₜ renSp o sp
  renSp o (_∷ₖ_ {B = B} t sp) =
    T.ren (⊆-of o) t ∷ₖ subst (λ x → Sp _ x _) (sub-ren-comm (⊆-of o) iz t B) (renSp o sp)

ren' : ∀ {Γ Δ Ξ A} → Δ ⊆[ T.id ] Ξ → Nf {Γ} Δ A → Nf Ξ A
ren' s t = subst (Nf _) (T.ren-id _) (ren s t)

renSp' : ∀ {Γ Δ Ξ A B} → Δ ⊆[ T.id ] Ξ → Sp {Γ} Δ A B → Sp Ξ A B
renSp' s t = subst₂ (Sp _) (T.ren-id _) (T.ren-id _) (renSp s t)

data Ix : ∀ {Γ} → T.Ix Γ → Con Γ → Set where
  iz   : ∀ {Γ Δ}     → Ix {Γ} iz Δ
  isₖ_ : ∀ {Γ Δ A i} → Ix {Γ} i Δ → Ix (is i) (Δ ▷ₖ A)
  isₜ_ : ∀ {Γ Δ A i} → Ix {Γ} i Δ → Ix i (Δ ▷ₜ A)

Ix-of : ∀ {Γ Δ i} → Ix {Γ} i Δ → T.Ix Γ
Ix-of {i = i} _ = i

insₖ : ∀ {Γ Δ i} A → Ix {Γ} i Δ → Con (ins Γ i A)
insₖ {Δ = Δ}      A iz      = Δ ▷ₖ A
insₖ {Δ = Δ ▷ₖ B} A (isₖ i) = insₖ A i ▷ₖ B
insₖ {Δ = Δ ▷ₜ B} A (isₜ i) = insₖ A i ▷ₜ T.ren (ins-⊆ _ (Ix-of i) A) B

insₜ : ∀ {Γ} Δ {i} → Ix i Δ → Ty (T.drop Γ i) ⋆ → Con Γ
insₜ Δ         iz      A = Δ ▷ₜ A
insₜ (Δ ▷ₖ B)  (isₖ i) A = insₜ Δ i A ▷ₖ B
insₜ (Δ ▷ₜ B)  (isₜ i) A = insₜ Δ i A ▷ₜ B

drop : ∀ {Γ i} → (Δ : Con Γ) → Ix {Γ} i Δ → Con (T.drop Γ i)
drop Δ        iz      = Δ
drop (Δ ▷ₖ _) (isₖ i) = drop Δ i
drop (Δ ▷ₜ _) (isₜ i) = drop Δ i

drop-⊆ : ∀ {Γ i} Δ (j : Ix {Γ} i Δ) → drop Δ j ⊆[ T.drop-⊆ Γ i ] Δ
drop-⊆ Δ        iz      = id
drop-⊆ (Δ ▷ₖ _) (isₖ j) = addₖ (drop-⊆ Δ j)
drop-⊆ (Δ ▷ₜ _) (isₜ j) = addₜ (drop-⊆ Δ j)

-- Normalization
--------------------------------------------------------------------------------

snocSpₜ : ∀ {Γ Δ A B C} → Sp {Γ} Δ A (B ⇒ C) → Nf Δ B → Sp Δ A C
snocSpₜ ε         t = t ∷ₜ ε
snocSpₜ (x ∷ₜ sp) t = x ∷ₜ snocSpₜ sp t
snocSpₜ (x ∷ₖ sp) t = x ∷ₖ snocSpₜ sp t

snocSpₖ : ∀ {Γ Δ A B C} → Sp {Γ} Δ A (∀' C) → (t : Ty Γ B) → Sp Δ A (inst t C)
snocSpₖ ε         t = t ∷ₖ ε
snocSpₖ (x ∷ₜ sp) t = x ∷ₜ snocSpₖ sp t
snocSpₖ (x ∷ₖ sp) t = x ∷ₖ snocSpₖ sp t

mutual
  η : ∀ {Γ Δ A} → A ∈ Δ → Nf {Γ} Δ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {Γ Δ A} → Ne {Γ} Δ A → Nf Δ A
  η-Ne {A = A ⇒ B} (v , sp) = ƛ η-Ne (vsₜ v , snocSpₜ (renSp' topᵗ sp) (η vz))
  η-Ne {A = ∀' B}  (v , sp) = {!!}
  η-Ne {A = ne _}  n        = ne n

mutual
  sub : ∀ {Γ i Δ A B}(j : Ix {Γ} i Δ) → Nf (drop Δ j) A → Nf (insₜ Δ j A) B → Nf Δ B
  sub j t' (ƛ t) = ƛ sub (isₜ j) t' t
  sub j t' (Λ t) = Λ sub (isₖ j) t' t
  sub j t' (ne (v , sp)) = {!!}


-- mutual
--   sub : ∀ {Γ A B} (i : Ix Γ) → Ty Γ A → Ty (ins Γ i A) B → Ty Γ B
--   sub i t' (A ⇒ B) = sub i t' A ⇒ sub i t' B
--   sub i t' (∀' A)  = ∀' (sub (is i) (ren top t') A)
--   sub i t' (ƛ t)   = ƛ (sub (is i) (ren top t') t)
--   sub i t' (ne (v , sp)) with ∈-eq i v | subSp i t' sp
--   ... | inj₁ refl | sp' = appSp t' sp'
--   ... | inj₂ v'   | sp' = ne (v' , sp')

--   subSp : ∀ {Γ A B C} (i : Ix Γ) → Ty Γ A → Sp (ins Γ i A) B C → Sp Γ B C
--   subSp i t' ε        = ε
--   subSp i t' (t ∷ sp) = sub i t' t ∷ subSp i t' sp

--   appSp : ∀ {Γ A B} → Ty Γ A → Sp Γ A B → Ty Γ B
--   appSp t ε            = t
--   appSp (ƛ t) (x ∷ sp) = appSp (sub iz x t) sp

-- inst : ∀ {Γ A B} → Ty Γ A → Ty (Γ ▷ A) B → Ty Γ B
-- inst = sub iz



