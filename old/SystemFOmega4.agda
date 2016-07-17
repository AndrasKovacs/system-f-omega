
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function

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

-- Types : OPE, renaming
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

idᵏ-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → idᵏ ∘ᵏ ι ≡ ι
idᵏ-∘  stop    = refl
idᵏ-∘ (add  ι) = cong add (idᵏ-∘ ι)
idᵏ-∘ (keep ι) = cong keep (idᵏ-∘ ι)

∘-idᵏ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ᵏ idᵏ ≡ ι
∘-idᵏ  stop    = refl
∘-idᵏ (add  ι) = cong add (∘-idᵏ ι)
∘-idᵏ (keep ι) = cong keep (∘-idᵏ ι)

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

ren-∈ₖ-id : ∀ {Γ σ} (v : σ ∈ₖ Γ) → ren-∈ₖ idᵏ v ≡ v
ren-∈ₖ-id  vz    = refl
ren-∈ₖ-id (vs v) = cong vs_ (ren-∈ₖ-id v)

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

ins : ∀ {Γ} → Ixₖ Γ → Kind → Conₖ
ins {Γ}     iz     A = Γ , A
ins {Γ , B} (is i) A = ins {Γ} i A , B

ins-⊆ : ∀ {Γ} (i : Ixₖ Γ) A → Γ ⊆ ins i A
ins-⊆ iz     A = top
ins-⊆ (is i) A = keep (ins-⊆ i A)

-- Types: normalization
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

-- Terms
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

-- Term OPE
--------------------------------------------------------------------------------

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

data _⊆[_]_ : ∀ {Γ Γ'} → Conₜ Γ → Γ ⊆ Γ' → Conₜ Γ' → Set where
  stop  : ε ⊆[ stop ] ε
  addₖ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ add s  ] (Ξ ,ₖ A)
  addₜ  : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → Δ        ⊆[ s      ] (Ξ ,ₜ A) -- rename?
  keepₖ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ,ₖ A) ⊆[ keep s ] (Ξ ,ₖ A)
  keepₜ : ∀ {Γ Γ'}{s : Γ ⊆ Γ'}{Δ Ξ A} → Δ ⊆[ s ] Ξ → (Δ ,ₜ A) ⊆[ s      ] (Ξ ,ₜ ren-NfTy s A)

⊆-of : ∀ {Γ Γ' Δ Ξ}{s : Γ ⊆ Γ'} → Δ ⊆[ s ] Ξ → Γ ⊆ Γ'
⊆-of {s = s} _ = s

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

data Ixₜ : ∀ {Γ} → Ixₖ Γ → Conₜ Γ → Set where
  iz   : ∀ {Γ Δ}     → Ixₜ {Γ} iz Δ
  isₖ_ : ∀ {Γ Δ A i} → Ixₜ {Γ} i Δ → Ixₜ (is i) (Δ ,ₖ A)
  isₜ_ : ∀ {Γ Δ A i} → Ixₜ {Γ} i Δ → Ixₜ i (Δ ,ₜ A)

Ixₖ-of : ∀ {Γ Δ i} → Ixₜ {Γ} i Δ → Ixₖ Γ
Ixₖ-of {i = i} _ = i

insₜₖ : ∀ {Γ Δ i} A → Ixₜ {Γ} i Δ → Conₜ (ins i A)
insₜₖ {Δ = Δ}      A iz      = Δ ,ₖ A
insₜₖ {Δ = Δ ,ₖ B} A (isₖ i) = insₜₖ A i ,ₖ B
insₜₖ {Δ = Δ ,ₜ B} A (isₜ i) = insₜₖ A i ,ₜ ren-NfTy (ins-⊆ (Ixₖ-of i) A) B

insₜₜ : ∀ {Γ Δ i} → NfTy Γ ⋆ → Ixₜ {Γ} i Δ → Conₜ Γ
insₜₜ {Δ = Δ}      A iz      = Δ ,ₜ A
insₜₜ {Δ = Δ ,ₖ B} A (isₖ i) = insₜₜ {!ren-NfTy ? A!} i ,ₖ B -- TODO: strip
insₜₜ {Δ = Δ ,ₜ B} A (isₜ i) = insₜₜ A i ,ₜ B

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

-- str-∈ₜ   B ∈ₜ




