{-# OPTIONS --without-K #-}

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Product

-- Kinds and types
--------------------------------------------------------------------------------

data Kind : Set where
  ⋆    : Kind
  _⇒_  : Kind → Kind → Kind
infixr 5 _⇒_   

data KCon : Set where
  ε   : KCon
  _,_ : KCon → Kind → KCon
-- infixr 4 _,_ -- from Data.Product  

data _∈ₖ_ (A : Kind) : KCon → Set where
  here  : ∀ {Γ} → A ∈ₖ (Γ , A)
  there : ∀ {Γ B} → A ∈ₖ Γ → A ∈ₖ Γ , B
infixr 4 _∈ₖ_

data Ty Γ : Kind → Set where
  _⇒_ : Ty Γ ⋆ → Ty Γ ⋆ → Ty Γ ⋆
  var : ∀ {A} → A ∈ₖ Γ → Ty Γ A
  _∙_ : ∀ {A B} → Ty Γ (A ⇒ B) → Ty Γ A → Ty Γ B
  λ'  : ∀ A {B} → Ty (Γ , A) B → Ty Γ (A ⇒ B)
  ∀'  : ∀ A → Ty (Γ , A) ⋆ → Ty Γ ⋆
infixl 6 _∙_

_-ₖ_ : ∀ {σ} Γ → σ ∈ₖ Γ → KCon
(Γ , σ) -ₖ here  = Γ
(Γ , σ) -ₖ there v = Γ -ₖ v , σ
infixl 6 _-ₖ_

wkVarₖ : ∀ {Γ A B} (v : A ∈ₖ Γ) → B ∈ₖ Γ -ₖ v → B ∈ₖ Γ
wkVarₖ here      v         = there v
wkVarₖ (there p) here      = here
wkVarₖ (there p) (there v) = there (wkVarₖ p v)

eqVarₖ :
  ∀ {Γ A B} (p : A ∈ₖ Γ)(q : B ∈ₖ Γ)
  → (∃ λ eq → subst (_∈ₖ Γ) eq p ≡ q) ⊎ (∃ λ q' → q ≡ wkVarₖ p q')
eqVarₖ here      here      = inj₁ (refl , refl)
eqVarₖ here      (there q) = inj₂ (q , refl)
eqVarₖ (there p) here      = inj₂ (here , refl)
eqVarₖ (there p) (there q) with eqVarₖ p q
eqVarₖ (there p) (there .p) | inj₁ (refl , refl) = inj₁ (refl , refl)
eqVarₖ (there p) (there ._) | inj₂ (q' , refl)   = inj₂ (there q' , refl)

wkTy : ∀ {Γ A B} (p : A ∈ₖ Γ) → Ty (Γ -ₖ p) B → Ty Γ B
wkTy p (A ⇒ B)  = wkTy p A ⇒ wkTy p B
wkTy p (var v)  = var (wkVarₖ p v)
wkTy p (f ∙ x)  = wkTy p f ∙ wkTy p x
wkTy p (λ' A t) = λ' A (wkTy (there p) t)
wkTy p (∀' A t) = ∀' A (wkTy (there p) t)

mutual 
  data NfTy Γ : Kind → Set where
    _⇒_ : NfTy Γ ⋆ → NfTy Γ ⋆ → NfTy Γ ⋆
    λ'  : ∀ A {B} → NfTy (Γ , A) B → NfTy Γ (A ⇒ B)
    ∀'  : ∀ A → NfTy (Γ , A) ⋆ → NfTy Γ ⋆    
    ne  : NeTy Γ ⋆ → NfTy Γ ⋆

  data NeTy Γ : Kind → Set where
    _,_ : ∀ {A B} → A ∈ₖ Γ → SpTy Γ A B → NeTy Γ B

  data SpTy Γ : Kind → Kind → Set where
    ε   : ∀ {A} → SpTy Γ A A
    _∷_ : ∀ {A B C} → NfTy Γ A → SpTy Γ B C → SpTy Γ (A ⇒ B) C
  infixr 5 _∷_

snocSpTy : ∀ {Γ A B C} → SpTy Γ A (B ⇒ C) → NfTy Γ B → SpTy Γ A C
snocSpTy ε       t = t ∷ ε
snocSpTy (x ∷ s) t = x ∷ snocSpTy s t

mutual  
  wkNfTy : ∀ {Γ A B} (v : A ∈ₖ Γ) → NfTy (Γ -ₖ v) B → NfTy Γ B
  wkNfTy v (a ⇒ b)        = wkNfTy v a ⇒ wkNfTy v b
  wkNfTy v (λ' A t)       = λ' A (wkNfTy (there v) t)
  wkNfTy v (∀' A t)       = ∀' A (wkNfTy (there v) t)
  wkNfTy v (ne (v' , sp)) = ne (wkVarₖ v v' , wkSpTy v sp)

  wkSpTy : ∀ {Γ A B C} (v : A ∈ₖ Γ) → SpTy (Γ -ₖ v) B C → SpTy Γ B C
  wkSpTy v ε        = ε
  wkSpTy v (t ∷ sp) = wkNfTy v t ∷ wkSpTy v sp

mutual
  η-Ty : ∀ {Γ A} → A ∈ₖ Γ → NfTy Γ A
  η-Ty x = η-NeTy (x , ε)

  η-NeTy : ∀ {A Γ} → NeTy Γ A → NfTy Γ A
  η-NeTy {⋆}     n        = ne n
  η-NeTy {A ⇒ B} (v , sp) = λ' A (η-NeTy (there v , snocSpTy (wkSpTy here sp) (η-Ty here)))

mutual
  substNfTy : ∀ {Γ A B} (v : A ∈ₖ Γ) → NfTy (Γ -ₖ v) A → NfTy Γ B → NfTy (Γ -ₖ v) B
  substNfTy v t' (a ⇒ b)  = substNfTy v t' a ⇒ substNfTy v t' b
  substNfTy v t' (λ' A t) = λ' A (substNfTy (there v) (wkNfTy here t') t)
  substNfTy v t' (∀' A t) = ∀' A (substNfTy (there v) (wkNfTy here t') t)
  substNfTy v t' (ne (v' , sp)) with eqVarₖ v v' | substSpTy v t' sp
  substNfTy v t' (ne (.v , sp)) | inj₁ (refl , refl) | sp' = appSpTy t' sp'
  substNfTy v t' (ne (._ , sp)) | inj₂ (v'' , refl)  | sp' = ne (v'' , sp')

  substSpTy : ∀ {Γ A B C} (v : A ∈ₖ Γ) → NfTy (Γ -ₖ v) A → SpTy Γ B C → SpTy (Γ -ₖ v) B C
  substSpTy v t' ε        = ε
  substSpTy v t' (x ∷ sp) = substNfTy v t' x ∷ substSpTy v t' sp

  instTy : ∀ {Γ A B} → NfTy Γ A → NfTy (Γ , A) B → NfTy Γ B
  instTy t' t = substNfTy here t' t

  appNfTy : ∀ {Γ A B} → NfTy Γ (A ⇒ B) → NfTy Γ A → NfTy Γ B
  appNfTy (λ' A t) x = instTy x t

  appSpTy : ∀ {Γ A B} → NfTy Γ A → SpTy Γ A B → NfTy Γ B
  appSpTy t      ε   = t
  appSpTy t (x ∷ sp) = appSpTy (appNfTy t x) sp

nfTy : ∀ {Γ A} → Ty Γ A → NfTy Γ A
nfTy (var v)  = η-Ty v
nfTy (∀' A t) = ∀' A (nfTy t)
nfTy (λ' A t) = λ' A (nfTy t)
nfTy (A ⇒ B)  = nfTy A ⇒ nfTy B
nfTy (f ∙ x)  = appNfTy (nfTy f) (nfTy x)

-- Terms
----------------------------------------------------------------------------------

data TCon : KCon → Set where
  ε    : TCon ε
  _,ₜ_ : ∀ {Γ} → TCon Γ → NfTy Γ ⋆ → TCon Γ
  _,ₖ_ : ∀ {Γ} → TCon Γ → (A : Kind) → TCon (Γ , A)
infixl 5 _,ₜ_ _,ₖ_

data _∈ₜ_ : ∀ {Γ} → NfTy Γ ⋆ → TCon Γ → Set where
  here : ∀ {Γ}{Δ : TCon Γ}{A}   → A ∈ₜ (Δ ,ₜ A)
  type : ∀ {Γ}{Δ : TCon Γ}{A B} → A ∈ₜ Δ → A ∈ₜ (Δ ,ₜ B)
  kind : ∀ {Γ}{Δ : TCon Γ}{A B} → A ∈ₜ Δ → wkNfTy here A ∈ₜ (Δ ,ₖ B)

_-ₜ_ : ∀ {Γ A} (Δ : TCon Γ) → A ∈ₜ Δ → TCon Γ
(Δ ,ₜ A) -ₜ here   = Δ
(Δ ,ₜ A) -ₜ type v = (Δ -ₜ v) ,ₜ A
(Δ ,ₖ A) -ₜ kind v = (Δ -ₜ v) ,ₖ A
infixl 6 _-ₜ_

data Tm {Γ} (Δ : TCon Γ) : NfTy Γ ⋆ → Set where
  var  : ∀ {A} → A ∈ₜ Δ → Tm Δ A
  λ'   : ∀ A {B} → Tm (Δ ,ₜ A) B → Tm Δ (A ⇒ B)
  _∙_  : ∀ {A B} → Tm Δ (A ⇒ B) → Tm Δ A → Tm Δ B
  Λ    : ∀ A {B} → Tm (Δ ,ₖ A) B → Tm Δ (∀' A B)
  _∙ₜ_ : ∀ {A B} → Tm Δ (∀' A B) → (t : NfTy Γ A) → Tm Δ (instTy t B)
infixl 6 _∙ₜ_

wkVarₜ : ∀ {Γ}{Δ : TCon Γ}{A B} (v : A ∈ₜ Δ) → B ∈ₜ (Δ -ₜ v) → B ∈ₜ Δ
wkVarₜ here     v'        = type v'
wkVarₜ (type v) here      = here
wkVarₜ (type v) (type v') = type (wkVarₜ v v')
wkVarₜ (kind v) (kind v') = kind (wkVarₜ v v')

eqVarₜ :
  ∀ {Γ}{Δ : TCon Γ}{A B}(p : A ∈ₜ Δ)(q : B ∈ₜ Δ)
  → (∃ λ eq → subst (_∈ₜ Δ) eq p ≡ q) ⊎ (∃ λ q' → q ≡ wkVarₜ p q')  
eqVarₜ here     here     = inj₁ (refl , refl)
eqVarₜ here     (type q) = inj₂ (q , refl)
eqVarₜ (type p) here     = inj₂ (here , refl)
eqVarₜ (type p) (type q) with eqVarₜ p q
eqVarₜ (type p) (type .p) | inj₁ (refl , refl) = inj₁ (refl , refl)
eqVarₜ (type p) (type ._) | inj₂ (q' , refl)   = inj₂ (type q' , refl)
eqVarₜ (kind p) (kind q) with eqVarₜ p q
eqVarₜ (kind p) (kind .p) | inj₁ (refl , refl) = inj₁ (refl , refl)
eqVarₜ (kind p) (kind ._) | inj₂ (q' , refl)   = inj₂ (kind q' , refl)

mutual
  data NfTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → Set where
    λ' : ∀ A {B} → NfTm (Δ ,ₜ A) B → NfTm Δ (A ⇒ B)
    Λ  : ∀ A {B} → NfTm (Δ ,ₖ A) B → NfTm Δ (∀' A B)
    ne : ∀ {n}   → NeTm Δ (ne n)   → NfTm Δ (ne n)

  data NeTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → Set where
    _,_ : ∀ {A B} → A ∈ₜ Δ → SpTm Δ A B → NeTm Δ B

  data SpTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → NfTy Γ ⋆ → Set where
    ε    : ∀ {A} → SpTm Δ A A
    _∷ₜ_ : ∀ {A B C} → NfTm Δ A → SpTm Δ B C → SpTm Δ (A ⇒ B) C
    _∷ₖ_ : ∀ {A B C} → (t : NfTy Γ A) → SpTm Δ (instTy t B) C → SpTm Δ (∀' A B) C
  infixr 5 _∷ₜ_ _∷ₖ_

snocSpTmₜ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (B ⇒ C) → NfTm Δ B → SpTm Δ A C
snocSpTmₜ ε         t = t ∷ₜ ε
snocSpTmₜ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₜ sp t
snocSpTmₜ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₜ sp t

snocSpTmₖ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (∀' B C) → (t : NfTy Γ B) → SpTm Δ A (instTy t C)
snocSpTmₖ ε         t = t ∷ₖ ε
snocSpTmₖ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₖ sp t
snocSpTmₖ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₖ sp t

mutual
  wkNfTmₜ : ∀ {Γ Δ A B}(v : A ∈ₜ Δ) → NfTm {Γ} (Δ -ₜ v) B → NfTm Δ B
  wkNfTmₜ v (λ' _ t)       = λ' _ (wkNfTmₜ (type v) t)
  wkNfTmₜ v (Λ _ t)        = Λ _ (wkNfTmₜ (kind v) t)
  wkNfTmₜ v (ne (v' , sp)) = ne (wkVarₜ v v' , wkSpTmₜ v sp)

  wkSpTmₜ : ∀ {Γ Δ A B C}(v : A ∈ₜ Δ) → SpTm {Γ} (Δ -ₜ v) B C → SpTm Δ B C
  wkSpTmₜ v ε         = ε
  wkSpTmₜ v (x ∷ₜ sp) = wkNfTmₜ v x ∷ₜ wkSpTmₜ v sp
  wkSpTmₜ v (t ∷ₖ sp) = t ∷ₖ wkSpTmₜ v sp

mutual
 η-Tm : ∀ {Γ Δ A} → A ∈ₜ Δ → NfTm {Γ} Δ A
 η-Tm v = η-NeTm (v , ε)

 η-NeTm : ∀ {Γ Δ A} → NeTm {Γ} Δ A → NfTm Δ A
 η-NeTm {A = A ⇒ B}  (v , sp) = λ' A (η-NeTm (type v , snocSpTmₜ (wkSpTmₜ here sp) (η-Tm here)))
 η-NeTm {A = ∀' A B} (v , sp) = Λ A (η-NeTm (kind v , snocSpTmₖ {!!} (η-Ty here)))
 η-NeTm {A = ne n}   t        = ne t


-- tests
--------------------------------------------------------------------------------

-- nv : ∀ {Γ A} → A ∈ₖ Γ → NfTy Γ A
-- nv = η-NfTy

-- nat : NfTy ε ⋆
-- nat = ∀' _ ((nv here ⇒ nv here) ⇒ nv here ⇒ nv here)

-- zero : Tm ε nat
-- zero = Λ _ (λ' _ (var here))

-- suc : Tm ε (nat ⇒ nat)
-- suc = λ' _ (Λ _ (λ' _ (λ' _
--     (var (type here)
--   ∙ (var (type (type (kind here))) ∙ₜ nv here ∙ var (type here) ∙ var here)))))

-- list : NfTy ε (⋆ ⇒ ⋆)
-- list = λ' _ (∀' _ ((nv (there here) ⇒ nv here ⇒ nv here) ⇒ nv here ⇒ nv here))

-- id' : Tm ε (∀' ⋆ (nv here ⇒ nv here))
-- id' = Λ _ (λ' _ (var here))

-- const' : Tm ε (∀' ⋆ (∀' ⋆ (nv (there here) ⇒ nv here ⇒ nv (there here))))
-- const' = Λ _ (Λ _ (λ' _ (λ' _ (var (type here)))))

-- const'' : Tm ε (∀' ⋆ (nv here ⇒ ∀' ⋆ (nv here ⇒ nv (there here))))
-- const'' = Λ _ (λ' _ (Λ _ (λ' _ (var (type (kind here))))))
