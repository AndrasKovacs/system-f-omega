open import Relation.Binary.PropositionalEquality

infixl 5 _,_
infix 3 _∋_
infix 4 _⊢_ 

data Con : Set
data Ty Γ : Set
data _∋_ : (Γ : Con) → Ty Γ → Set
data _⊢_ (Γ : Con) : Ty Γ → Set
data _⊆_ : Con → Con → Set

data Con where
  ε   : Con
  _,_ : (Γ : Con) (A : Ty Γ) → Con

data Ty Γ where
  U  : Ty Γ
  El : (t : Γ ⊢ U) → Ty Γ

id       : ∀ {Γ} → Γ ⊆ Γ
renTy    : ∀ {Γ Δ} → Γ ⊆ Δ → Ty Γ → Ty Δ
ren-∈    : ∀ {Γ Δ A} → (o : Γ ⊆ Δ) → Γ ∋ A → Δ ∋ renTy o A
renTm    : ∀ {Γ Δ A} → (o : Γ ⊆ Δ) → Γ ⊢ A → Δ ⊢ renTy o A
renTy-id : ∀ {Γ} (A : Ty Γ) → renTy id A ≡ A

data _⊆_ where
  stop : ε ⊆ ε
  add  : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ⊆ (Δ , A)
  keep : ∀ {Γ Δ A} → (o : Γ ⊆ Δ) → (Γ , A) ⊆ (Δ , renTy o A)

_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ o'      = o'
add  o ∘ o'      = add (o ∘ o')
keep o ∘ add o'  = add (o ∘ o')
keep o ∘ keep o' = {!keep (o ∘ o')!}

-- _∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
-- stop   ∘ ι      = ι
-- add  κ ∘ ι      = add  (κ ∘ ι)
-- keep κ ∘ add  ι = add  (κ ∘ ι)
-- keep κ ∘ keep ι = keep (κ ∘ ι)

data _∋_ where
  vz   : ∀{Γ}{A : Ty Γ} → Γ , A ∋ renTy (add id) A
  vs_  : ∀{Γ}{A B : Ty Γ} → Γ ∋ A → Γ , B ∋ renTy (add id) A

data _⊢_ Γ where
  var : ∀ {A} → Γ ∋ A → Γ ⊢ A

ren-∈ stop ()
ren-∈ {Γ}{Δ , B}{A} (add o) v = {!vs ren-∈ o v!}
ren-∈ (keep o) v = {!!}

renTy o U       = U
renTy o (El t)  = {!!}
renTm o (var v) = {!!}

id {ε}     = stop
id {Γ , A} = subst (λ x → (Γ , A) ⊆ (Γ , x)) (renTy-id A) (keep id )

renTy-id = {!!}


