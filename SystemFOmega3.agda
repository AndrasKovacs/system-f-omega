{-# OPTIONS --without-K #-}

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.List hiding (drop)

-- goal : insertion and (prepend) weakening commutes
--        define multiple prepend weakening

-- Kinds and types
--------------------------------------------------------------------------------

data Kind : Set where
  ⋆    : Kind
  _⇒_  : Kind → Kind → Kind
infixr 5 _⇒_   

data Conₖ : Set where
  ε   : Conₖ
  _,_ : Conₖ → Kind → Conₖ
infixl 4 _,_

data Ixₖ : Conₖ → Set where
  here  : ∀ {Γ} → Ixₖ Γ
  there : ∀ {Γ A} → Ixₖ Γ → Ixₖ (Γ , A)

data _∈ₖ_ (A : Kind) : Conₖ → Set where
  here  : ∀ {Γ} → A ∈ₖ (Γ , A)
  there : ∀ {Γ B} → A ∈ₖ Γ → A ∈ₖ (Γ , B)
infixr 3 _∈ₖ_

data Ty Γ : Kind → Set where
  _⇒_ : Ty Γ ⋆ → Ty Γ ⋆ → Ty Γ ⋆
  var : ∀ {A} → A ∈ₖ Γ → Ty Γ A
  _∙_ : ∀ {A B} → Ty Γ (A ⇒ B) → Ty Γ A → Ty Γ B
  λ'  : ∀ A {B} → Ty (Γ , A) B → Ty Γ (A ⇒ B)
  ∀'  : ∀ A → Ty (Γ , A) ⋆ → Ty Γ ⋆
infixl 6 _∙_

ins : ∀ Γ → Ixₖ Γ → Kind → Conₖ
ins Γ       here      A = Γ , A
ins (Γ , B) (there i) A = ins Γ i A , B

_<><_ : Conₖ → List Kind → Conₖ
Γ <>< []       = Γ
Γ <>< (k ∷ ks) = (Γ , k) <>< ks

shift-∈ : ∀ {Γ A} Ξ → A ∈ₖ Γ → A ∈ₖ (Γ <>< Ξ)
shift-∈ []       v = v
shift-∈ (k ∷ ks) v = shift-∈ ks (there v)

-- shiftTy : ∀ {Γ A Ξ} → (∀ Ξ' A → A ∈ₖ (Γ <>< Ξ') → A ∈ₖ ((Γ <>< Ξ) <>< Ξ')) → Ty Γ A → Ty (Γ <>< Ξ) A
-- shiftTy ren (t ⇒ t₁) = {!!}
-- shiftTy ren (var x) = {!!}
-- shiftTy ren (t ∙ t₁) = {!!}
-- shiftTy {Γ}{A ⇒ B}{Ξ} ren (λ' .A t) = λ' A {!shiftTy!}
-- shiftTy ren (∀' A t) = {!!}


wk-∈ : ∀ {B Γ A} i → A ∈ₖ Γ → A ∈ₖ ins Γ i B
wk-∈ here      v         = there v
wk-∈ (there i) here      = here
wk-∈ (there i) (there v) = there (wk-∈ i v)

wkTy : ∀ B {Γ A} i → Ty Γ A → Ty (ins Γ i B) A
wkTy _ i (A ⇒ B)  = wkTy _ i A ⇒ wkTy _ i B
wkTy _ i (var v)  = var (wk-∈ i v)
wkTy _ i (f ∙ x)  = wkTy _ i f ∙ wkTy _ i x
wkTy _ i (λ' A t) = λ' A (wkTy _ (there i) t)
wkTy _ i (∀' A t) = ∀' A (wkTy _ (there i) t)

-- shiftTy : ∀ {Γ A} i → Ty (drop Γ i) A → Ty Γ A
-- shiftTy i (a ⇒ b) = shiftTy i a ⇒ shiftTy i b
-- shiftTy i (var v) = var (shift-∈ i v)
-- shiftTy i (f ∙ x) = shiftTy i f ∙ shiftTy i x
-- shiftTy {Γ}{A ⇒ B} i (λ' _ t) = λ' _ {!shiftTy {Γ , A}{B} (there i)!}
-- shiftTy i (∀' A t) = {!!}

-- wk-∈-comm :
--   ∀ {Γ A B B'}(d : Ixₖ Γ)(v : A ∈ₖ drop Γ d) (i : Ixₖ (drop Γ d))
--   →  wk-∈ {B} here (wk-∈ {B'} i v) ≡ wk-∈ {B'} (there i) (wk-∈ here v)
-- wk-∈-comm d v i = {!!}

wk-∈-comm :
  ∀ {Γ A B B'}(v : A ∈ₖ Γ) i → 
  wk-∈ {B} here (wk-∈ {B'} i v) ≡ wk-∈ {B'} (there i) (wk-∈ here v)
wk-∈-comm v i = refl

wkTy-comm :
  ∀ {Γ A B B'} i (t : Ty Γ A)
  → wkTy B here (wkTy B' i t) ≡ wkTy B' (there i) (wkTy _ here t)
wkTy-comm i (a ⇒ b) = cong₂ _⇒_ (wkTy-comm i a) (wkTy-comm i b)
wkTy-comm i (var _) = refl
wkTy-comm i (f ∙ x) = cong₂ _∙_ (wkTy-comm i f) (wkTy-comm i x)
wkTy-comm {Γ}{A ⇒ B}{C}{D} i (λ' .A t) = {!cong (λ' A) (wkTy-comm {Γ , A}{B}{A}{D} (there i) t)!}
wkTy-comm i (∀' A t) = {!wkTy (there here) (wkTy (there i) t)!}  


-- wk-∈ₖ : ∀ {Γ Δ A B} → Γ ▶ B ≡ Δ → A ∈ₖ Γ → A ∈ₖ Δ
-- wk-∈ₖ here      v         = there v
-- wk-∈ₖ (there w) here      = here
-- wk-∈ₖ (there w) (there v) = there (wk-∈ₖ w v)

-- str-∈ₖ : ∀ {Γ Δ A B} → Γ ▶ A ≡ Δ → B ∈ₖ Δ → (A ≡ B) ⊎ (B ∈ₖ Γ)
-- str-∈ₖ here      here      = inj₁ refl
-- str-∈ₖ here      (there v) = inj₂ v
-- str-∈ₖ (there w) here      = inj₂ here
-- str-∈ₖ (there w) (there v) = map id there (str-∈ₖ w v)

-- wkTy : ∀ {Γ Δ A B} → Γ ▶ B ≡ Δ → Ty Γ A → Ty Δ A 
-- wkTy p (A ⇒ B)  = wkTy p A ⇒ wkTy p B
-- wkTy p (var v)  = var (wk-∈ₖ p v)
-- wkTy p (f ∙ x)  = wkTy p f ∙ wkTy p x
-- wkTy p (λ' A t) = λ' A (wkTy (there p) t)
-- wkTy p (∀' A t) = ∀' A (wkTy (there p) t)

-- mutual 
--   data NfTy Γ : Kind → Set where
--     _⇒_ : NfTy Γ ⋆ → NfTy Γ ⋆ → NfTy Γ ⋆
--     λ'  : ∀ A {B} → NfTy (Γ , A) B → NfTy Γ (A ⇒ B)
--     ∀'  : ∀ A → NfTy (Γ , A) ⋆ → NfTy Γ ⋆    
--     ne  : NeTy Γ ⋆ → NfTy Γ ⋆

--   data NeTy Γ : Kind → Set where
--     _,_ : ∀ {A B} → A ∈ₖ Γ → SpTy Γ A B → NeTy Γ B

--   data SpTy Γ : Kind → Kind → Set where
--     ε   : ∀ {A} → SpTy Γ A A
--     _∷_ : ∀ {A B C} → NfTy Γ A → SpTy Γ B C → SpTy Γ (A ⇒ B) C
--   infixr 5 _∷_

-- snocSpTy : ∀ {Γ A B C} → SpTy Γ A (B ⇒ C) → NfTy Γ B → SpTy Γ A C
-- snocSpTy ε       t = t ∷ ε
-- snocSpTy (x ∷ s) t = x ∷ snocSpTy s t

-- mutual  
--   wkNfTy : ∀ {Γ Δ A B} → Γ ▶ B ≡ Δ → NfTy Γ A → NfTy Δ A
--   wkNfTy w (A ⇒ B)       = wkNfTy w A ⇒ wkNfTy w B
--   wkNfTy w (λ' A t)      = λ' A (wkNfTy (there w) t)
--   wkNfTy w (∀' A t)      = ∀' A (wkNfTy (there w) t)
--   wkNfTy w (ne (v , sp)) = ne (wk-∈ₖ w v , wkSpTy w sp)

--   wkSpTy : ∀ {Γ Δ A B C} → Γ ▶ C ≡ Δ → SpTy Γ A B → SpTy Δ A B
--   wkSpTy w ε        = ε
--   wkSpTy w (x ∷ sp) = wkNfTy w x ∷ wkSpTy w sp

-- mutual
--   η-Ty : ∀ {Γ A} → A ∈ₖ Γ → NfTy Γ A
--   η-Ty v = η-NeTy (v , ε)

--   η-NeTy : ∀ {A Γ} → NeTy Γ A → NfTy Γ A
--   η-NeTy {⋆}     n        = ne n
--   η-NeTy {A ⇒ B} (v , sp) = λ' A (η-NeTy (there v , snocSpTy (wkSpTy here sp) (η-Ty here)))

-- mutual
--   substNfTy : ∀ {Γ Δ A B} → Γ ▶ A ≡ Δ → NfTy Γ A → NfTy Δ B → NfTy Γ B  
--   substNfTy w t' (A ⇒ B)  = substNfTy w t' A ⇒ substNfTy w t' B
--   substNfTy w t' (λ' A t) = λ' A (substNfTy (there w) (wkNfTy here t') t)
--   substNfTy w t' (∀' A t) = ∀' A (substNfTy (there w) (wkNfTy here t') t)
--   substNfTy w t' (ne (v , sp)) with str-∈ₖ w v | substSpTy w t' sp
--   ... | inj₁ refl | sp' = appSpTy t' sp'
--   ... | inj₂ v'   | sp' = ne (v' , sp')

--   substSpTy : ∀ {Γ Δ A B C} → Γ ▶ A ≡ Δ → NfTy Γ A → SpTy Δ B C → SpTy Γ B C
--   substSpTy w t' ε        = ε
--   substSpTy w t' (x ∷ sp) = substNfTy w t' x ∷ substSpTy w t' sp

--   instTy : ∀ {Γ A B} → NfTy Γ A → NfTy (Γ , A) B → NfTy Γ B
--   instTy = substNfTy here

--   appTy : ∀ {Γ A B} → NfTy Γ (A ⇒ B) → NfTy Γ A → NfTy Γ B
--   appTy (λ' A f) x = instTy x f

--   appSpTy : ∀ {Γ A B} → NfTy Γ A → SpTy Γ A B → NfTy Γ B
--   appSpTy t ε        = t
--   appSpTy t (x ∷ sp) = appSpTy (appTy t x) sp

-- nfTy : ∀ {Γ A} → Ty Γ A → NfTy Γ A
-- nfTy (var v)  = η-Ty v
-- nfTy (∀' A t) = ∀' A (nfTy t)
-- nfTy (λ' A t) = λ' A (nfTy t)
-- nfTy (A ⇒ B)  = nfTy A ⇒ nfTy B
-- nfTy (f ∙ x)  = appTy (nfTy f) (nfTy x)

-- -- Terms
-- ----------------------------------------------------------------------------------

-- data Conₜ : Conₖ → Set where
--   ε    : Conₜ ε
--   _,ₜ_ : ∀ {Γ} → Conₜ Γ → NfTy Γ ⋆ → Conₜ Γ
--   _,ₖ_ : ∀ {Γ} → Conₜ Γ → (A : Kind) → Conₜ (Γ , A)
-- infixl 5 _,ₜ_ _,ₖ_

-- data _∈ₜ_ : ∀ {Γ} → NfTy Γ ⋆ → Conₜ Γ → Set where
--   here : ∀ {Γ}{Δ : Conₜ Γ}{A}   → A ∈ₜ (Δ ,ₜ A)
--   type : ∀ {Γ}{Δ : Conₜ Γ}{A B} → A ∈ₜ Δ → A ∈ₜ (Δ ,ₜ B)
--   kindk : ∀ {Γ}{Δ : Conₜ Γ}{A B} → A ∈ₜ Δ → wkNfTy here A ∈ₜ (Δ ,ₖ B)

-- data Tm {Γ} (Δ : Conₜ Γ) : NfTy Γ ⋆ → Set where
--   var  : ∀ {A} → A ∈ₜ Δ → Tm Δ A
--   λ'   : ∀ A {B} → Tm (Δ ,ₜ A) B → Tm Δ (A ⇒ B)
--   _∙_  : ∀ {A B} → Tm Δ (A ⇒ B) → Tm Δ A → Tm Δ B
--   Λ    : ∀ A {B} → Tm (Δ ,ₖ A) B → Tm Δ (∀' A B)
--   _∙ₜ_ : ∀ {A B} → Tm Δ (∀' A B) → (t : NfTy Γ A) → Tm Δ (instTy t B)
-- infixl 6 _∙ₜ_

-- data _▶ₜ_≡_ : ∀ {Γ} → Conₜ Γ → NfTy Γ ⋆ → Conₜ Γ → Set where
--   here : ∀ {Γ}{Δ : Conₜ Γ}{A} → Δ ▶ₜ A ≡ (Δ ,ₜ A)
--   type : ∀ {Γ}{Δ Δ' : Conₜ Γ}{A B} → Δ ▶ₜ A ≡ Δ' → (Δ ,ₜ B) ▶ₜ A ≡ (Δ' ,ₜ B)
--   kind : ∀ {Γ}{Δ Δ' : Conₜ Γ}{A B} → Δ ▶ₜ A ≡ Δ' → (Δ ,ₖ B) ▶ₜ wkNfTy here A ≡ (Δ' ,ₖ B)
-- infix 3 _▶ₜ_≡_

-- data _▶ₖ_≡_ : ∀ {Γ Γ' A} → Conₜ Γ → Γ ▶ A ≡ Γ' → Conₜ Γ' → Set where
--   here : ∀ {Γ}{Δ : Conₜ Γ}{A} → Δ ▶ₖ here ≡ (Δ ,ₖ A)
--   type : ∀ {Γ Γ' A B}{w : Γ ▶ A ≡ Γ'}{Δ Δ'} → Δ ▶ₖ w ≡ Δ' → (Δ ,ₜ B) ▶ₖ w ≡ (Δ' ,ₜ wkNfTy w B)
--   kind : ∀ {Γ Γ' A B}{w : Γ ▶ A ≡ Γ'}{Δ Δ'} → Δ ▶ₖ w ≡ Δ' → (Δ ,ₖ B) ▶ₖ (there w) ≡ (Δ' ,ₖ B)

-- wk-∈ₜₜ : ∀ {Γ}{Δ Δ' : Conₜ Γ}{A B} → Δ ▶ₜ A ≡ Δ' → B ∈ₜ Δ → B ∈ₜ Δ'
-- wk-∈ₜₜ here     v        = type v
-- wk-∈ₜₜ (type w) here     = here
-- wk-∈ₜₜ (type w) (type v) = type (wk-∈ₜₜ w v)
-- wk-∈ₜₜ (kind w) (kindk v) = kindk (wk-∈ₜₜ w v)

-- wk-∈ₜₖ : ∀ {Γ Γ' Δ Δ' A B}{w : Γ ▶ A ≡ Γ'} → Δ ▶ₖ w ≡ Δ' → B ∈ₜ Δ → wkNfTy w B ∈ₜ Δ'
-- wk-∈ₜₖ here      v        = kindk v
-- wk-∈ₜₖ (type w) here      = here
-- wk-∈ₜₖ (type w) (type v)  = type (wk-∈ₜₖ w v)
-- wk-∈ₜₖ (kind w) (kindk v) = {!kindk (wk-∈ₜₖ w v)!}



-- wk-∈ₜₜ : ∀ {Γ}{Δ : Conₜ Γ}{A B} → 

-- : ∀ {Γ}{Δ : TCon Γ}{A B} (v : A ∈ₜ Δ) → B ∈ₜ (Δ -ₜ v) → B ∈ₜ Δ

-- wkVarₜ : ∀ {Γ}{Δ : TCon Γ}{A B} (v : A ∈ₜ Δ) → B ∈ₜ (Δ -ₜ v) → B ∈ₜ Δ
-- wkVarₜ here     v'        = type v'
-- wkVarₜ (type v) here      = here
-- wkVarₜ (type v) (type v') = type (wkVarₜ v v')
-- wkVarₜ (kind v) (kind v') = kind (wkVarₜ v v')

-- eqVarₜ :
--   ∀ {Γ}{Δ : TCon Γ}{A B}(p : A ∈ₜ Δ)(q : B ∈ₜ Δ)
--   → (∃ λ eq → subst (_∈ₜ Δ) eq p ≡ q) ⊎ (∃ λ q' → q ≡ wkVarₜ p q')  
-- eqVarₜ here     here     = inj₁ (refl , refl)
-- eqVarₜ here     (type q) = inj₂ (q , refl)
-- eqVarₜ (type p) here     = inj₂ (here , refl)
-- eqVarₜ (type p) (type q) with eqVarₜ p q
-- eqVarₜ (type p) (type .p) | inj₁ (refl , refl) = inj₁ (refl , refl)
-- eqVarₜ (type p) (type ._) | inj₂ (q' , refl)   = inj₂ (type q' , refl)
-- eqVarₜ (kind p) (kind q) with eqVarₜ p q
-- eqVarₜ (kind p) (kind .p) | inj₁ (refl , refl) = inj₁ (refl , refl)
-- eqVarₜ (kind p) (kind ._) | inj₂ (q' , refl)   = inj₂ (kind q' , refl)

-- mutual
--   data NfTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → Set where
--     λ' : ∀ A {B} → NfTm (Δ ,ₜ A) B → NfTm Δ (A ⇒ B)
--     Λ  : ∀ A {B} → NfTm (Δ ,ₖ A) B → NfTm Δ (∀' A B)
--     ne : ∀ {n}   → NeTm Δ (ne n)   → NfTm Δ (ne n)

--   data NeTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → Set where
--     _,_ : ∀ {A B} → A ∈ₜ Δ → SpTm Δ A B → NeTm Δ B

--   data SpTm {Γ}(Δ : TCon Γ) : NfTy Γ ⋆ → NfTy Γ ⋆ → Set where
--     ε    : ∀ {A} → SpTm Δ A A
--     _∷ₜ_ : ∀ {A B C} → NfTm Δ A → SpTm Δ B C → SpTm Δ (A ⇒ B) C
--     _∷ₖ_ : ∀ {A B C} → (t : NfTy Γ A) → SpTm Δ (instTy t B) C → SpTm Δ (∀' A B) C
--   infixr 5 _∷ₜ_ _∷ₖ_

-- snocSpTmₜ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (B ⇒ C) → NfTm Δ B → SpTm Δ A C
-- snocSpTmₜ ε         t = t ∷ₜ ε
-- snocSpTmₜ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₜ sp t
-- snocSpTmₜ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₜ sp t

-- snocSpTmₖ : ∀ {Γ Δ A B C} → SpTm {Γ} Δ A (∀' B C) → (t : NfTy Γ B) → SpTm Δ A (instTy t C)
-- snocSpTmₖ ε         t = t ∷ₖ ε
-- snocSpTmₖ (x ∷ₜ sp) t = x ∷ₜ snocSpTmₖ sp t
-- snocSpTmₖ (x ∷ₖ sp) t = x ∷ₖ snocSpTmₖ sp t

-- mutual
--   wkNfTmₜ : ∀ {Γ Δ A B}(v : A ∈ₜ Δ) → NfTm {Γ} (Δ -ₜ v) B → NfTm Δ B
--   wkNfTmₜ v (λ' _ t)       = λ' _ (wkNfTmₜ (type v) t)
--   wkNfTmₜ v (Λ _ t)        = Λ _ (wkNfTmₜ (kind v) t)
--   wkNfTmₜ v (ne (v' , sp)) = ne (wkVarₜ v v' , wkSpTmₜ v sp)

--   wkSpTmₜ : ∀ {Γ Δ A B C}(v : A ∈ₜ Δ) → SpTm {Γ} (Δ -ₜ v) B C → SpTm Δ B C
--   wkSpTmₜ v ε         = ε
--   wkSpTmₜ v (x ∷ₜ sp) = wkNfTmₜ v x ∷ₜ wkSpTmₜ v sp
--   wkSpTmₜ v (t ∷ₖ sp) = t ∷ₖ wkSpTmₜ v sp

-- mutual
--  η-Tm : ∀ {Γ Δ A} → A ∈ₜ Δ → NfTm {Γ} Δ A
--  η-Tm v = η-NeTm (v , ε)

--  η-NeTm : ∀ {Γ Δ A} → NeTm {Γ} Δ A → NfTm Δ A
--  η-NeTm {A = A ⇒ B}  (v , sp) = λ' A (η-NeTm (type v , snocSpTmₜ (wkSpTmₜ here sp) (η-Tm here)))
--  η-NeTm {A = ∀' A B} (v , sp) = Λ A (η-NeTm (kind v , snocSpTmₖ {!!} (η-Ty here)))
--  η-NeTm {A = ne n}   t        = ne t


-- -- tests
-- --------------------------------------------------------------------------------

-- -- nv : ∀ {Γ A} → A ∈ₖ Γ → NfTy Γ A
-- -- nv = η-NfTy

-- -- nat : NfTy ε ⋆
-- -- nat = ∀' _ ((nv here ⇒ nv here) ⇒ nv here ⇒ nv here)

-- -- zero : Tm ε nat
-- -- zero = Λ _ (λ' _ (var here))

-- -- suc : Tm ε (nat ⇒ nat)
-- -- suc = λ' _ (Λ _ (λ' _ (λ' _
-- --     (var (type here)
-- --   ∙ (var (type (type (kind here))) ∙ₜ nv here ∙ var (type here) ∙ var here)))))

-- -- list : NfTy ε (⋆ ⇒ ⋆)
-- -- list = λ' _ (∀' _ ((nv (there here) ⇒ nv here ⇒ nv here) ⇒ nv here ⇒ nv here))

-- -- id' : Tm ε (∀' ⋆ (nv here ⇒ nv here))
-- -- id' = Λ _ (λ' _ (var here))

-- -- const' : Tm ε (∀' ⋆ (∀' ⋆ (nv (there here) ⇒ nv here ⇒ nv (there here))))
-- -- const' = Λ _ (Λ _ (λ' _ (λ' _ (var (type here)))))

-- -- const'' : Tm ε (∀' ⋆ (nv here ⇒ ∀' ⋆ (nv here ⇒ nv (there here))))
-- -- const'' = Λ _ (λ' _ (Λ _ (λ' _ (var (type (kind here))))))
