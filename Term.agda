
module SystemFOmega.Term where

open import SystemFOmega.Type
  hiding (Con; _∈_; ren-∈; id; Ne; η-Ne; η; Sp; ren;
          renSp; sub; drop;  ∈-eq; subSp; subᶜ; _◇_; drop-sub-⊆; inst)
import SystemFOmega.Type as T

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum

open import Function using (_$_)
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
   T.ren (⊆-of o) t ∷ₖ
   subst (λ x → Sp _ x _) (ren-sub vz (keep (⊆-of o)) t B) (renSp o sp)

ren' : ∀ {Γ Δ Ξ A} → Δ ⊆[ T.id ] Ξ → Nf {Γ} Δ A → Nf Ξ A
ren' s t = subst (Nf _) (T.ren-id _) (ren s t)

renSp' : ∀ {Γ Δ Ξ A B} → Δ ⊆[ T.id ] Ξ → Sp {Γ} Δ A B → Sp Ξ A B
renSp' s t = subst₂ (Sp _) (T.ren-id _) (T.ren-id _) (renSp s t)

dropᶜᵏ : ∀ {Γ}{Δ : Con Γ}{A} → A ∈ Δ → T.Con
dropᶜᵏ {Γ}vz = Γ
dropᶜᵏ (vsₜ v) = dropᶜᵏ v
dropᶜᵏ (vsₖ v) = dropᶜᵏ v

dropᶜᵏ-⊆ : ∀ {Γ}{Δ : Con Γ}{A}(v : A ∈ Δ) → dropᶜᵏ v ⊆ Γ
dropᶜᵏ-⊆ vz      = T.id
dropᶜᵏ-⊆ (vsₜ v) = dropᶜᵏ-⊆ v
dropᶜᵏ-⊆ (vsₖ v) = add (dropᶜᵏ-⊆ v)

dropᶜᵗ : ∀ {Γ}{Δ : Con Γ}{A} → (v : A ∈ Δ) → Con (dropᶜᵏ v)
dropᶜᵗ {_}{Δ ▷ₜ _} vz = Δ
dropᶜᵗ (vsₜ v) = dropᶜᵗ v
dropᶜᵗ (vsₖ v) = dropᶜᵗ v

dropᵗ : ∀ {Γ}{Δ : Con Γ}{A} → (v : A ∈ Δ) → Ty (dropᶜᵏ v) ⋆
dropᵗ {A = A} vz = A
dropᵗ (vsₜ v) = dropᵗ v
dropᵗ (vsₖ v) = dropᵗ v


-- Normalization
--------------------------------------------------------------------------------

snocSpₜ : ∀ {Γ Δ A B C} → Sp {Γ} Δ A (B ⇒ C) → Nf Δ B → Sp Δ A C
snocSpₜ ε         t = t ∷ₜ ε
snocSpₜ (x ∷ₜ sp) t = x ∷ₜ snocSpₜ sp t
snocSpₜ (x ∷ₖ sp) t = x ∷ₖ snocSpₜ sp t

snocSpₖ : ∀ {Γ Δ A B C} → Sp {Γ} Δ A (∀' C) → (t : Ty Γ B) → Sp Δ A (T.inst t C)
snocSpₖ ε         t = t ∷ₖ ε
snocSpₖ (x ∷ₜ sp) t = x ∷ₜ snocSpₖ sp t
snocSpₖ (x ∷ₖ sp) t = x ∷ₖ snocSpₖ sp t

subᶜᵗ : ∀ {Γ}{Δ : Con Γ}{A} → A ∈ Δ → Con Γ
subᶜᵗ {_}{Δ ▷ₜ _} vz     = Δ
subᶜᵗ {_}{Δ ▷ₜ A}(vsₜ v) = subᶜᵗ v ▷ₜ A
subᶜᵗ {_}{Δ ▷ₖ A}(vsₖ v) = subᶜᵗ v ▷ₖ A

subᶜᵏ : ∀ {Γ A}(v : A T.∈ Γ)(t : T.Ty (T.drop v) A) → Con Γ → Con (T.subᶜ v)
subᶜᵏ ()     t ε
subᶜᵏ v      t (Δ ▷ₜ A) = subᶜᵏ v t Δ ▷ₜ T.sub v t A
subᶜᵏ vz     t (Δ ▷ₖ A) = Δ
subᶜᵏ (vs v) t (Δ ▷ₖ A) = subᶜᵏ v t Δ ▷ₖ A

∈-eq : ∀ {Γ}{Δ : Con Γ}{A B}(v : A ∈ Δ) (v' : B ∈ Δ) → (A ≡ B) ⊎ (B ∈ subᶜᵗ v)
∈-eq vz      vz       = inj₁ refl
∈-eq vz      (vsₜ v') = inj₂ v'
∈-eq (vsₜ v) vz       = inj₂ vz
∈-eq (vsₜ v) (vsₜ v') with ∈-eq v v'
... | inj₁ refl = inj₁ refl
... | inj₂ v''  = inj₂ (vsₜ v'')
∈-eq (vsₖ v) (vsₖ v') with ∈-eq v v'
... | inj₁ refl = inj₁ refl
... | inj₂ v''  = inj₂ (vsₖ v'')

drop-sub-⊆ : ∀ {Γ}{Δ : Con Γ}{A}(v : A ∈ Δ) → dropᶜᵗ v ⊆[ dropᶜᵏ-⊆ v ] subᶜᵗ v
drop-sub-⊆ vz      = id
drop-sub-⊆ (vsₜ v) = addₜ (drop-sub-⊆ v)
drop-sub-⊆ (vsₖ v) = addₖ (drop-sub-⊆ v)

ren-drop : ∀ {Γ Δ A}(v : A ∈ Δ) → T.ren (dropᶜᵏ-⊆ v) (dropᵗ {Γ} v) ≡ A
ren-drop vz      = ren-id _
ren-drop (vsₜ v) = ren-drop v
ren-drop (vsₖ v) =
  trans
    (trans
      (cong (λ x → T.ren (add x) (dropᵗ v)) (sym $ T.id-∘ (dropᶜᵏ-⊆ v)))
      (sym $ T.ren-∘ top (dropᶜᵏ-⊆ v) (dropᵗ v)))
    (cong (T.ren top) (ren-drop v))

undrop : ∀ {Γ}{Δ : Con Γ}{A}(v : A ∈ Δ) → Nf (dropᶜᵗ v) (dropᵗ v) → Nf (subᶜᵗ v) A
undrop v t = subst (Nf _) (ren-drop v) (ren (drop-sub-⊆ v) t)

∈-sub :
  ∀ {Γ}{Δ : Con Γ}{κ A} (vk : κ T.∈ Γ)(t' : Ty (T.drop vk) κ)
  → A ∈ Δ → T.sub vk t' A ∈ subᶜᵏ vk t' Δ
∈-sub {Δ = ε}      _  _       ()
∈-sub {Δ = Δ ▷ₜ t} vz t'      vz      = vz
∈-sub {Δ = Δ ▷ₜ t} vz t'      (vsₜ v) = vsₜ ∈-sub vz t' v
∈-sub {Δ = Δ ▷ₜ A} (vs vk) t' vz      = vz
∈-sub {Δ = Δ ▷ₜ t} (vs vk) t' (vsₜ v) = vsₜ ∈-sub (vs vk) t' v
∈-sub {Δ = Δ ▷ₖ κ} vz      t' (vsₖ v) = subst (_∈ _) (sym (inst-top t' _)) v
∈-sub {Δ = Δ ▷ₖ B} (vs vk) t' (vsₖ_ {A = A} v) =
   subst (_∈ _) (ren-top-sub vk t' A) (vsₖ (∈-sub vk t' v))

mutual
  η : ∀ {Γ Δ A} → A ∈ Δ → Nf {Γ} Δ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {Γ Δ A} → Ne {Γ} Δ A → Nf Δ A
  η-Ne {A = A ⇒ B} (v , sp) = ƛ η-Ne (vsₜ v , snocSpₜ (renSp' topᵗ sp) (η vz))
  η-Ne {Δ = Δ}{A = ∀'_ {A} B}  (v , sp) =
    Λ η-Ne (vsₖ v ,
      subst (Sp _ _) {!!} (snocSpₖ (renSp (topᵏ{A}) sp) (T.η vz))) -- η-eq plz
  η-Ne {A = ne _} n = ne n

mutual
  subₖ :
    ∀ {Γ Δ A B}(v : A T.∈ Γ) (t' : Ty (T.drop v) A)
    → Nf {Γ} Δ B → Nf (subᶜᵏ v t' Δ) (T.sub v t' B)
  subₖ v t' (ƛ t) = ƛ subₖ v t' t
  subₖ v t' (Λ t) = Λ subₖ (vs v) t' t
  subₖ v t' (ne {v'ₜ , _} (v' , sp)) with T.∈-eq v v'ₜ | subSpₖ v t' sp
  ... | inj₁ refl | sp' = η-Ne (∈-sub v t' v' , sp')
  ... | inj₂ v''  | sp' = ne (∈-sub v t' v' , sp')

  subSpₖ :
    ∀ {Γ Δ A B C}(v : A T.∈ Γ) (t' : Ty (T.drop v) A)
    → Sp {Γ} Δ B C → Sp (subᶜᵏ v t' Δ) (T.sub v t' B) (T.sub v t' C)
  subSpₖ v t' ε         = ε
  subSpₖ v t' (t ∷ₜ sp) = subₖ  v t' t ∷ₜ subSpₖ v t' sp
  subSpₖ v t' (k ∷ₖ sp) = T.sub v t' k ∷ₖ
    subst (λ x → Sp _ x _) {!drop-sub-⊆ !} (subSpₖ v t' sp) -- sub-sub comm plz

mutual
  {-# TERMINATING #-} -- and why?? The call graph is the same as in STLC sub
  subₜ :
    ∀ {Γ Δ A B} (v : A ∈ Δ) → Nf (dropᶜᵗ v) (dropᵗ v) → Nf {Γ} Δ B → Nf (subᶜᵗ v) B
  subₜ v t' (ƛ t)  = ƛ subₜ (vsₜ v) t' t
  subₜ v t' (Λ t)  = Λ subₜ (vsₖ v) t' t
  subₜ v t' (ne (v' , sp)) with ∈-eq v v' | subSpₜ v t' sp
  ... | inj₁ refl | sp' = undrop v t' ◇ sp'
  ... | inj₂ v''  | sp' = ne (v'' , sp')

  subSpₜ :
    ∀ {Γ Δ A B C} (v : A ∈ Δ) → Nf (dropᶜᵗ v) (dropᵗ v) → Sp {Γ} Δ B C → Sp (subᶜᵗ v) B C
  subSpₜ v t' ε         = ε
  subSpₜ v t' (x ∷ₜ sp) = subₜ v t' x ∷ₜ subSpₜ v t' sp
  subSpₜ v t' (t ∷ₖ sp) = t           ∷ₖ subSpₜ v t' sp

  _◇_ : ∀ {Γ Δ A B} → Nf {Γ} Δ A → Sp Δ A B → Nf Δ B
  t     ◇ ε          = t
  (ƛ t) ◇ (t' ∷ₜ sp) = subₜ vz t' t ◇ sp
  (Λ t) ◇ (k  ∷ₖ sp) = subₖ vz k  t ◇ sp

nf : ∀ {Γ Δ A} → Tm {Γ} Δ A → Nf Δ A
nf (var v)  = η v
nf (ƛ t)    = ƛ nf t
nf (Λ t)    = Λ nf t
nf (f ∙ x)  with nf f
... | ƛ f' = subₜ vz (nf x) f'
nf (f ∙ₜ x) with nf f
... | Λ f' = subₖ vz x f'

