
module SystemFOmega.Type where

open import Data.Sum renaming (map to smap)
open import Function using (_$_; _∋_)
open import Relation.Binary.PropositionalEquality

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
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

id : ∀ {Γ} → Γ ⊆ Γ
id {ε}     = stop
id {Γ ▷ _} = keep id

top : ∀ {A Γ} → Γ ⊆ (Γ ▷ A)
top = add id

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop ()
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep o) vz     = vz
ren-∈ (keep o) (vs v) = vs ren-∈ o v

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
drop-sub-⊆ vz     = id
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

⊆-drop : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → drop v ⊆ drop (ren-∈ o v)
⊆-drop  ()    stop
⊆-drop  v     (add o)  = ⊆-drop v o
⊆-drop  vz    (keep o) = o
⊆-drop  (vs v)(keep o) = ⊆-drop v o

⊆-subᶜ : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → subᶜ v ⊆ subᶜ (ren-∈ o v)
⊆-subᶜ ()     stop
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

_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ ι      = ι
add  κ ∘ ι      = add  (κ ∘ ι)
keep κ ∘ add  ι = add  (κ ∘ ι)
keep κ ∘ keep ι = keep (κ ∘ ι)

id-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → id ∘ ι ≡ ι
id-∘  stop    = refl
id-∘ (add  ι) = cong add (id-∘ ι)
id-∘ (keep ι) = cong keep (id-∘ ι)

∘-id : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ id ≡ ι
∘-id  stop    = refl
∘-id (add  ι) = cong add (∘-id ι)
∘-id (keep ι) = cong keep (∘-id ι)

ren-∈-id : ∀ {Γ A} (v : A ∈ Γ) → ren-∈ id v ≡ v
ren-∈-id  vz    = refl
ren-∈-id (vs v) = cong vs_ (ren-∈-id v)

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (o : Δ ⊆ Ξ) (o' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ o (ren-∈ o' v) ≡ ren-∈ (o ∘ o') v
ren-∈-∘  stop     stop     ()
ren-∈-∘ (add  o)  o'        v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (add  o')  v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (keep o')  vz    = refl
ren-∈-∘ (keep o) (keep o') (vs v) = cong vs_ (ren-∈-∘ o o' v)

mutual
  ren-∘ : ∀ {Γ Δ Ξ A}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(t : Ty Γ A) → ren o (ren o' t) ≡ ren (o ∘ o') t
  ren-∘ o o' (A ⇒ B)       = cong₂ _⇒_ (ren-∘ o o' A) (ren-∘ o o' B)
  ren-∘ o o' (∀' A)        = cong ∀'_ (ren-∘ (keep o) (keep o') A)
  ren-∘ o o' (ƛ  t)        = cong ƛ_ (ren-∘ (keep o) (keep o') t)
  ren-∘ o o' (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-∘ o o' v) (renSp-∘ o o' sp)

  renSp-∘ :
    ∀ {Γ Δ Ξ A B}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(sp : Sp Γ A B)
    → renSp o (renSp o' sp) ≡ renSp (o ∘ o') sp
  renSp-∘ o o' ε        = refl
  renSp-∘ o o' (t ∷ sp) = cong₂ _∷_ (ren-∘ o o' t) (renSp-∘ o o' sp)

mutual
  ren-id : ∀ {Γ A}(t : Ty Γ A) → ren id t ≡ t
  ren-id (A ⇒ B)       = cong₂ _⇒_ (ren-id A) (ren-id B)
  ren-id (ƛ t)         = cong ƛ_ (ren-id t)
  ren-id (∀' t)        = cong ∀'_ (ren-id t)
  ren-id (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-id v) (renSp-id sp)

  renSp-id : ∀ {Γ A B}(sp : Sp Γ A B) → renSp id sp ≡ sp
  renSp-id ε        = refl
  renSp-id (t ∷ sp) = cong₂ _∷_ (ren-id t) (renSp-id sp)


