
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

infixr 9 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
refl   ∘ o'      = o'
add o  ∘ o'      = add (o ∘ o')
keep o ∘ refl    = keep o
keep o ∘ add o'  = add (o ∘ o')
keep o ∘ keep o' = keep (o ∘ o')

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

infixr 5 _++_
_++_ : ∀ {Γ A B C} → Sp Γ A B → Sp Γ B C → Sp Γ A C
_++_ ε        ys = ys
_++_ (x ∷ xs) ys = x ∷ xs ++ ys

mutual
  η : ∀ {Γ A} → A ∈ Γ → Ty Γ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {A Γ} → Ne Γ A → Ty Γ A
  η-Ne {⋆}     n        = ne n
  η-Ne {A ⇒ B} (v , sp) = ƛ η-Ne ((vs v) , (renSp top sp ++ η vz ∷ ε))

