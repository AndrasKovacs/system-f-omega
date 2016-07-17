
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Function

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ , A)
  vs_ : ∀ {Γ B} → A ∈ Γ → A ∈ (Γ , B)

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A}   → A ∈ Γ → Tm Γ A
  λ'  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  _∙_ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

data _⊆_ : Con → Con → Set where
  stop : ε ⊆ ε
  skip : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ , A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ , A) ⊆ (Δ , A)

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop     v      = v
ren-∈ (skip r) v      = vs (ren-∈ r v)
ren-∈ (keep r) vz     = vz
ren-∈ (keep r) (vs v) = vs (ren-∈ r v)

ren-Tm : ∀ {Γ Δ A} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
ren-Tm r (var v) = var (ren-∈ r v)
ren-Tm r (λ' t)  = λ' (ren-Tm (keep r) t)
ren-Tm r (f ∙ x) = ren-Tm r f ∙ ren-Tm r x

_∘ˢ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

idˢ : ∀ {Γ} → Γ ⊆ Γ
idˢ {ε}     = stop
idˢ {Γ , A} = keep idˢ

top : ∀ {A Γ} → Γ ⊆ (Γ , A)
top = skip idˢ

idˢ-∘ˢ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → idˢ ∘ˢ ι ≡ ι
idˢ-∘ˢ  stop    = refl
idˢ-∘ˢ (skip ι) = cong skip (idˢ-∘ˢ ι)
idˢ-∘ˢ (keep ι) = cong keep (idˢ-∘ˢ ι)

∘ˢ-idˢ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ˢ idˢ ≡ ι
∘ˢ-idˢ  stop    = refl
∘ˢ-idˢ (skip ι) = cong skip (∘ˢ-idˢ ι)
∘ˢ-idˢ (keep ι) = cong keep (∘ˢ-idˢ ι)

ren-∈-idˢ : ∀ {Γ σ} (v : σ ∈ Γ) → ren-∈ idˢ v ≡ v
ren-∈-idˢ  vz    = refl
ren-∈-idˢ (vs v) = cong vs_ (ren-∈-idˢ v)

ren-∈-∘ˢ :
  ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ)
  → ren-∈ κ (ren-∈ ι v) ≡ ren-∈ (κ ∘ˢ ι) v
ren-∈-∘ˢ  stop     stop     ()
ren-∈-∘ˢ (skip κ)  ι        v     = cong vs_ (ren-∈-∘ˢ κ ι v)
ren-∈-∘ˢ (keep κ) (skip ι)  v     = cong vs_ (ren-∈-∘ˢ κ ι v)
ren-∈-∘ˢ (keep κ) (keep ι)  vz    = refl
ren-∈-∘ˢ (keep κ) (keep ι) (vs v) = cong vs_ (ren-∈-∘ˢ κ ι v)

ren-Tm-∘ˢ :
  ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (t : Tm Γ σ)
  → ren-Tm κ (ren-Tm ι t) ≡ ren-Tm (κ ∘ˢ ι) t
ren-Tm-∘ˢ κ ι (var v) = cong var (ren-∈-∘ˢ κ ι v)
ren-Tm-∘ˢ κ ι (λ' t)  = cong λ' (ren-Tm-∘ˢ (keep κ) (keep ι) t)
ren-Tm-∘ˢ κ ι (f ∙ x) = cong₂ _∙_ (ren-Tm-∘ˢ κ ι f) (ren-Tm-∘ˢ κ ι x)  

⊆-comm-Tm :
  ∀ {Γ Γ' A B} (s : Γ ⊆ Γ')(t : Tm Γ A)
  → ren-Tm (keep {B} s) (ren-Tm (top {B}) t)
  ≡ ren-Tm (top {B}) (ren-Tm s t)
⊆-comm-Tm {B = B} s t rewrite
    ren-Tm-∘ˢ (keep {B} s) (top {B}) t
  | ren-Tm-∘ˢ (top {B}) s t
  | ∘ˢ-idˢ s
  | idˢ-∘ˢ s
  = refl

