
module SystemFOmega.Type where

open import Data.Sum renaming (map to smap)
open import Function using (_$_; _∋_)
import Function as F
open import Relation.Binary.PropositionalEquality

open import Data.Unit
open import Data.Empty

data Kind : Set where
  ⋆   : Kind
  _⇒_ : Kind → Kind → Kind
infixr 2 _⇒_

data Con : Set where
  ε   : Con
  _▷_ : Con → Kind → Con
infixl 4 _▷_

data _∈_ A : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs_ : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▷ B)

mutual
  data Ty Γ : Kind → Set where
    _⇒_ : Ty Γ ⋆ → Ty Γ ⋆ → Ty Γ ⋆
    ƛ_  : ∀ {A B} → Ty (Γ ▷ A) B → Ty Γ (A ⇒ B)
    ∀'_ : ∀ {A}   → Ty (Γ ▷ A) ⋆ → Ty Γ ⋆
    ne  : Ne Γ ⋆ → Ty Γ ⋆

  data Ne Γ : Kind → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B

  data Sp Γ : Kind → Kind → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Ty Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 5 _∷_

data _⊆_ : Con → Con → Set where
  refl : ∀ {Γ} → Γ ⊆ Γ
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

top : ∀ {A Γ} → Γ ⊆ (Γ ▷ A)
top = add refl

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ refl     v      = v
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep o) vz     = vz
ren-∈ (keep o) (vs v) = vs ren-∈ o v

vs-∈-≡ :
  ∀ {Γ}{A : Set}{B C} {v v' : A ⊎ (B ∈ Γ)}
  → v ≡ v' → smap F.id (vs_ {B = C}) v ≡ smap F.id vs_ v'
vs-∈-≡ = cong (smap F.id vs_)

mutual
  ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Ty Γ A → Ty Δ A
  ren o (A ⇒ B)       = ren o A ⇒ ren o B
  ren o (∀' t)        = ∀' ren (keep o) t
  ren o (ƛ t)         = ƛ (ren (keep o) t)
  ren o (ne (v , sp)) = ne ((ren-∈ o v) , renSp o sp)

  renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
  renSp o ε        = ε
  renSp o (x ∷ sp) = ren o x ∷ renSp o sp

drop : ∀ {Γ A} → A ∈ Γ → Con
drop {Γ ▷ _} vz     = Γ
drop {Γ ▷ _} (vs v) = drop v

drop-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ Γ
drop-⊆ vz     = top
drop-⊆ (vs v) = add (drop-⊆ v)

subᶜ : ∀ {Γ A} → A ∈ Γ → Con
subᶜ {Γ ▷ _} vz     = Γ
subᶜ {Γ ▷ A} (vs v) = subᶜ v ▷ A

subᶜ-⊆ : ∀ {Γ A} (v : A ∈ Γ) → subᶜ v ⊆ Γ
subᶜ-⊆ vz     = top
subᶜ-⊆ (vs v) = keep (subᶜ-⊆ v)

drop-sub-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ subᶜ v
drop-sub-⊆ vz     = refl
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

⊆-drop : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → drop v ⊆ drop (ren-∈ o v)
⊆-drop v      refl     = refl
⊆-drop v      (add o)  = ⊆-drop v o
⊆-drop vz     (keep o) = o
⊆-drop (vs v) (keep o) = ⊆-drop v o

⊆-subᶜ : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → subᶜ v ⊆ subᶜ (ren-∈ o v)
⊆-subᶜ v      refl     = refl
⊆-subᶜ v      (add o)  = add (⊆-subᶜ v o)
⊆-subᶜ vz     (keep o) = o
⊆-subᶜ (vs v) (keep o) = keep (⊆-subᶜ v o)

∈-eq : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ Γ) → (A ≡ B) ⊎ (B ∈ subᶜ v)
∈-eq vz     vz      = inj₁ refl
∈-eq vz     (vs v') = inj₂ v'
∈-eq (vs v) vz      = inj₂ vz
∈-eq (vs v) (vs v') = smap (λ z → z) vs_ (∈-eq v v')

mutual
  sub : ∀ {Γ A B} → (v : A ∈ Γ) → Ty (drop v) A → Ty Γ B → Ty (subᶜ v) B
  sub v t' (A ⇒ B) = sub v t' A ⇒ sub v t' B
  sub v t' (∀' t)  = ∀' sub (vs v) t' t
  sub v t' (ƛ t)   = ƛ  sub (vs v) t' t
  sub v t' (ne (v' , sp)) with ∈-eq v v' | subSp v t' sp
  ... | inj₁ refl | sp' = ren (drop-sub-⊆ v) t' ◇ sp'
  ... | inj₂ v''  | sp' = ne (v'' , sp')

  subSp : ∀ {Γ A B C} → (v : A ∈ Γ) → Ty (drop v) A → Sp Γ B C → Sp (subᶜ v) B C
  subSp v t' ε        = ε
  subSp v t' (t ∷ sp) = sub v t' t ∷ subSp v t' sp

  _◇_ : ∀ {Γ A B} → Ty Γ A → Sp Γ A B → Ty Γ B
  t     ◇ ε        = t
  (ƛ t) ◇ (x ∷ sp) = sub vz x t ◇ sp

inst : ∀ {Γ A B} → Ty Γ A → Ty (Γ ▷ A) B → Ty Γ B
inst = sub vz

snocSp : ∀ {Γ A B C} → Sp Γ A (B ⇒ C) → Ty Γ B → Sp Γ A C
snocSp ε       t = t ∷ ε
snocSp (x ∷ s) t = x ∷ snocSp s t

mutual
  η : ∀ {Γ A} → A ∈ Γ → Ty Γ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {A Γ} → Ne Γ A → Ty Γ A
  η-Ne {⋆}     n        = ne n
  η-Ne {A ⇒ B} (v , sp) = ƛ η-Ne ((vs v) , snocSp (renSp top sp) (η vz))

-- Categorical stuff for _⊆_
--------------------------------------------------------------------------------

infixr 9 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
refl   ∘ o'      = o'
add o  ∘ o'      = add (o ∘ o')
keep o ∘ refl    = keep o
keep o ∘ add o'  = add (o ∘ o')
keep o ∘ keep o' = keep (o ∘ o')

∘-refl : ∀ {Γ Δ} (o : Γ ⊆ Δ) → o ∘ refl ≡ o
∘-refl refl     = refl
∘-refl (add o)  = cong add (∘-refl o)
∘-refl (keep o) = refl

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (o : Δ ⊆ Ξ) (o' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ o (ren-∈ o' v) ≡ ren-∈ (o ∘ o') v
ren-∈-∘ refl     o'        v      = refl
ren-∈-∘ (add o)  o'        v      = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) refl      v      = refl
ren-∈-∘ (keep o) (add o')  v      = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (keep o') vz     = refl
ren-∈-∘ (keep o) (keep o') (vs v) = ren-∈-∘ (add o) o' v

mutual
  ren-∘ : ∀ {Γ Δ Ξ A}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(t : Ty Γ A) → ren o (ren o' t) ≡ ren (o ∘ o') t
  ren-∘ o o' (A ⇒ B)       = cong₂ _⇒_ (ren-∘ o o' A) (ren-∘ o o' B)
  ren-∘ o o' (∀' A)        = cong ∀'_  (ren-∘ (keep o) (keep o') A)
  ren-∘ o o' (ƛ  t)        = cong ƛ_   (ren-∘ (keep o) (keep o') t)
  ren-∘ o o' (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-∘ o o' v) (renSp-∘ o o' sp)

  renSp-∘ :
    ∀ {Γ Δ Ξ A B}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(sp : Sp Γ A B)
    → renSp o (renSp o' sp) ≡ renSp (o ∘ o') sp
  renSp-∘ o o' ε        = refl
  renSp-∘ o o' (t ∷ sp) = cong₂ _∷_ (ren-∘ o o' t) (renSp-∘ o o' sp)

Id-⊆ : ∀ {Γ} → Γ ⊆ Γ → Set
Id-⊆ refl     = ⊤
Id-⊆ (add o)  = ⊥
Id-⊆ (keep o) = Id-⊆ o

ren-∈-Id : ∀ {Γ A}(o : Γ ⊆ Γ){{p : Id-⊆ o}}(v : A ∈ Γ) → ren-∈ o v ≡ v
ren-∈-Id refl     v      = refl
ren-∈-Id (add o) {{()}} v
ren-∈-Id (keep o) vz     = refl
ren-∈-Id (keep o) (vs v) = cong vs_ (ren-∈-Id o v)

mutual
  ren-Id : ∀ {Γ A}(o : Γ ⊆ Γ){{p : Id-⊆ o}}(t : Ty Γ A) → ren o t ≡ t
  ren-Id o (A ⇒ B)       = cong₂ _⇒_ (ren-Id o A) (ren-Id o B)
  ren-Id o (ƛ t)         = cong ƛ_ (ren-Id (keep o) t)
  ren-Id o (∀' t)        = cong ∀'_ (ren-Id (keep o) t)
  ren-Id o (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-Id o v) (renSp-Id o sp)

  renSp-Id : ∀ {Γ A B}(o : Γ ⊆ Γ){{p : Id-⊆ o}}(sp : Sp Γ A B) → renSp o sp ≡ sp
  renSp-Id o ε        = refl
  renSp-Id o (t ∷ sp) = cong₂ _∷_ (ren-Id o t) (renSp-Id o sp)

ren-refl : ∀ {Γ A}(t : Ty Γ A) → ren refl t ≡ t
ren-refl = ren-Id refl

renSp-refl : ∀ {Γ A B}(sp : Sp Γ A B) → renSp refl sp ≡ sp
renSp-refl = renSp-Id refl


