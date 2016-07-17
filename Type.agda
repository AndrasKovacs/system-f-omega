{-# OPTIONS --without-K #-}

module SystemFOmega.Type where

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function

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
  iz  : ∀ {Γ} → Ixₖ Γ
  is_ : ∀ {Γ A} → Ixₖ Γ → Ixₖ (Γ , A)

data _∈ₖ_ (A : Kind) : Conₖ → Set where
  vz  : ∀ {Γ} → A ∈ₖ (Γ , A)
  vs_ : ∀ {Γ B} → A ∈ₖ Γ → A ∈ₖ (Γ , B)
infixr 3 _∈ₖ_

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

-- Renaming
--------------------------------------------------------------------------------

data _⊆_ : Conₖ → Conₖ → Set where
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ , A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ , A) ⊆ (Δ , A)

_∘ᵏ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ᵏ ι      = ι
add  κ ∘ᵏ ι      = add (κ ∘ᵏ ι)
keep κ ∘ᵏ add  ι = add (κ ∘ᵏ ι)
keep κ ∘ᵏ keep ι = keep (κ ∘ᵏ ι)

idᵏ : ∀ {Γ} → Γ ⊆ Γ
idᵏ {ε}     = stop
idᵏ {Γ , A} = keep idᵏ

top : ∀ {A Γ} → Γ ⊆ (Γ , A)
top = add idᵏ

ren-∈ₖ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ₖ Γ → A ∈ₖ Δ
ren-∈ₖ stop ()
ren-∈ₖ (add  r) v      = vs (ren-∈ₖ r v)
ren-∈ₖ (keep r) vz     = vz
ren-∈ₖ (keep r) (vs v) = vs (ren-∈ₖ r v)

mutual
  ren-NfTy : ∀ {Γ Δ A} → Γ ⊆ Δ → NfTy Γ A → NfTy Δ A
  ren-NfTy s (a ⇒ b)       = ren-NfTy s a ⇒ ren-NfTy s b
  ren-NfTy s (λ' A t)      = λ' A (ren-NfTy (keep s) t)
  ren-NfTy s (∀' A t)      = ∀' A (ren-NfTy (keep s) t)
  ren-NfTy s (ne (v , sp)) = ne (ren-∈ₖ s v , ren-SpTy s sp)

  ren-SpTy : ∀ {Γ Δ A B} → Γ ⊆ Δ → SpTy Γ A B → SpTy Δ A B
  ren-SpTy s ε        = ε
  ren-SpTy s (t ∷ sp) = ren-NfTy s t ∷ ren-SpTy s sp

drop : ∀ {Γ} → Ixₖ Γ → Conₖ
drop {Γ}     iz     = Γ
drop {Γ , _} (is i) = drop i

ins : ∀ {Γ} → Ixₖ Γ → Kind → Conₖ
ins {Γ}     iz     A = Γ , A
ins {Γ , B} (is i) A = ins {Γ} i A , B

ins-⊆ : ∀ {Γ} (i : Ixₖ Γ) A → Γ ⊆ ins i A
ins-⊆ iz     A = top
ins-⊆ (is i) A = keep (ins-⊆ i A)

drop-⊆ : ∀ {Γ} i → drop {Γ} i ⊆ Γ
drop-⊆ iz     = idᵏ
drop-⊆ (is i) = add (drop-⊆ i)

-- Normalization
--------------------------------------------------------------------------------

snocSpTy : ∀ {Γ A B C} → SpTy Γ A (B ⇒ C) → NfTy Γ B → SpTy Γ A C
snocSpTy ε       t = t ∷ ε
snocSpTy (x ∷ s) t = x ∷ snocSpTy s t

str-∈ₖ : ∀ {Γ A B} i → B ∈ₖ (ins {Γ} i A) → (A ≡ B) ⊎ (B ∈ₖ Γ)
str-∈ₖ iz     vz     = inj₁ refl
str-∈ₖ iz     (vs v) = inj₂ v
str-∈ₖ (is i) vz     = inj₂ vz
str-∈ₖ (is i) (vs v) = map id vs_ (str-∈ₖ i v)

mutual
  η-Ty : ∀ {Γ A} → A ∈ₖ Γ → NfTy Γ A
  η-Ty x = η-NeTy (x , ε)

  η-NeTy : ∀ {A Γ} → NeTy Γ A → NfTy Γ A
  η-NeTy {⋆}     n        = ne n
  η-NeTy {A ⇒ B} (v , sp) = λ' A (η-NeTy (vs v , snocSpTy (ren-SpTy top sp) (η-Ty vz)))

mutual
  substNfTy : ∀ {Γ A B} (i : Ixₖ Γ) → NfTy Γ A → NfTy (ins i A) B → NfTy Γ B
  substNfTy i t' (a ⇒ b)       = substNfTy i t' a ⇒ substNfTy i t' b
  substNfTy i t' (λ' A t)      = λ' A (substNfTy (is i) (ren-NfTy top t') t)
  substNfTy i t' (∀' A t)      = ∀' A (substNfTy (is i) (ren-NfTy top t') t)
  substNfTy i t' (ne (v , sp)) with str-∈ₖ i v | substSpTy i t' sp
  ... | inj₁ refl | sp' = appSpTy t' sp'
  ... | inj₂ v'   | sp' = ne (v' , sp')

  substSpTy : ∀ {Γ A B C} (i : Ixₖ Γ) → NfTy Γ A → SpTy (ins i A) B C → SpTy Γ B C
  substSpTy i t' ε        = ε
  substSpTy i t' (t ∷ sp) = substNfTy i t' t ∷ substSpTy i t' sp

  instTy : ∀ {Γ A B} → NfTy Γ A → NfTy (Γ , A) B → NfTy Γ B
  instTy t' t = substNfTy iz t' t

  appNfTy : ∀ {Γ A B} → NfTy Γ (A ⇒ B) → NfTy Γ A → NfTy Γ B
  appNfTy (λ' A t) x = instTy x t

  appSpTy : ∀ {Γ A B} → NfTy Γ A → SpTy Γ A B → NfTy Γ B
  appSpTy t      ε   = t
  appSpTy t (x ∷ sp) = appSpTy (appNfTy t x) sp


-- Proofs
--------------------------------------------------------------------------------

ren-∈ₖ-id : ∀ {Γ σ} (v : σ ∈ₖ Γ) → ren-∈ₖ idᵏ v ≡ v
ren-∈ₖ-id  vz    = refl
ren-∈ₖ-id (vs v) = cong vs_ (ren-∈ₖ-id v)

mutual
  ren-NfTy-id : ∀ {Γ A} (t : NfTy Γ A) → ren-NfTy idᵏ t ≡ t
  ren-NfTy-id (a ⇒ b)       = cong₂ _⇒_ (ren-NfTy-id a) (ren-NfTy-id b)
  ren-NfTy-id (λ' A t)      = cong (λ' A) (ren-NfTy-id t)
  ren-NfTy-id (∀' A t)      = cong (∀' A) (ren-NfTy-id t)
  ren-NfTy-id (ne (v , sp)) =
    cong₂ (λ a b → ne (a , b)) (ren-∈ₖ-id v) (ren-SpTy-id sp)

  ren-SpTy-id : ∀ {Γ A B} (sp : SpTy Γ A B) → ren-SpTy idᵏ sp ≡ sp
  ren-SpTy-id ε        = refl
  ren-SpTy-id (x ∷ sp) = cong₂ _∷_ (ren-NfTy-id x) (ren-SpTy-id sp)

idᵏ-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → idᵏ ∘ᵏ ι ≡ ι
idᵏ-∘  stop    = refl
idᵏ-∘ (add  ι) = cong add (idᵏ-∘ ι)
idᵏ-∘ (keep ι) = cong keep (idᵏ-∘ ι)

∘-idᵏ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ᵏ idᵏ ≡ ι
∘-idᵏ  stop    = refl
∘-idᵏ (add  ι) = cong add (∘-idᵏ ι)
∘-idᵏ (keep ι) = cong keep (∘-idᵏ ι)

ren-∈ₖ-∘ :
  ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (v : σ ∈ₖ Γ)
  → ren-∈ₖ κ (ren-∈ₖ ι v) ≡ ren-∈ₖ (κ ∘ᵏ ι) v
ren-∈ₖ-∘  stop     stop     ()
ren-∈ₖ-∘ (add  κ)  ι        v     = cong vs_ (ren-∈ₖ-∘ κ ι v)
ren-∈ₖ-∘ (keep κ) (add  ι)  v     = cong vs_ (ren-∈ₖ-∘ κ ι v)
ren-∈ₖ-∘ (keep κ) (keep ι)  vz    = refl
ren-∈ₖ-∘ (keep κ) (keep ι) (vs v) = cong vs_ (ren-∈ₖ-∘ κ ι v)

mutual
  ren-NfTy-∘ :
    ∀ {Γ Δ Ξ A} (s' : Δ ⊆ Ξ) (s : Γ ⊆ Δ) (t : NfTy Γ A)
    → ren-NfTy s' (ren-NfTy s t) ≡ ren-NfTy (s' ∘ᵏ s) t
  ren-NfTy-∘ s' s (a ⇒ b)       = cong₂ _⇒_ (ren-NfTy-∘ s' s a) (ren-NfTy-∘ s' s b)
  ren-NfTy-∘ s' s (λ' A t)      = cong (λ' A) (ren-NfTy-∘ (keep s') (keep s) t)
  ren-NfTy-∘ s' s (∀' A t)      = cong (∀' A) (ren-NfTy-∘ (keep s') (keep s) t)
  ren-NfTy-∘ s' s (ne (v , sp)) = cong₂ (λ a b → ne (a , b)) (ren-∈ₖ-∘ s' s v) (ren-SpTy-∘ s' s sp)

  ren-SpTy-∘ :
    ∀ {Γ Δ Ξ A B} (s' : Δ ⊆ Ξ) (s : Γ ⊆ Δ) (t : SpTy Γ A B)
    → ren-SpTy s' (ren-SpTy s t) ≡ ren-SpTy (s' ∘ᵏ s) t
  ren-SpTy-∘ s' s ε        = refl
  ren-SpTy-∘ s' s (t ∷ sp) = cong₂ _∷_ (ren-NfTy-∘ s' s t) (ren-SpTy-∘ s' s sp)

top-add :
  ∀ {Γ Δ B} A (s : Γ ⊆ Δ) (t : NfTy Γ B)
  → ren-NfTy (top {A}) (ren-NfTy s t) ≡ ren-NfTy (add {A} s) t
top-add A s t rewrite
    ren-NfTy-∘ (top {A}) s t
  | idᵏ-∘ s
  = refl

keep-top :
  ∀ {Γ Δ B} A (s : Γ ⊆ Δ)(t : NfTy Γ B)
  → ren-NfTy (top {A}) (ren-NfTy s t) ≡ ren-NfTy (keep {A} s) (ren-NfTy (top {A}) t)
keep-top A s t rewrite
    ren-NfTy-∘ (keep {A} s) (top {A}) t
  | ren-NfTy-∘ (add {A} idᵏ) s t
  | idᵏ-∘ s
  | ∘-idᵏ s
  = refl


