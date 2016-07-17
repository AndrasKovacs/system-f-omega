
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Function

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty
infixr 2 _⇒_  

data Con : Set where
  ε   : Con
  _,_ : Con → Ty → Con
infixl 3 _,_

data _∈_ (A : Ty) : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ , A)
  vs_ : ∀ {Γ B} → A ∈ Γ → A ∈ (Γ , B)

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A}   → A ∈ Γ → Tm Γ A
  λ'  : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  _∙_ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
infixl 8 _∙_

mutual
  data Nf Γ : Ty → Set where
    λ'  : ∀ A {B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
    ne  : Ne Γ ⋆ → Nf Γ ⋆
  
  data Ne Γ : Ty → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B
  
  data Sp Γ : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 5 _∷_

data Sub (Γ : Con) : Con → Set where
  ε   : Sub Γ ε
  _,_ : ∀ {Δ A} → Sub Γ Δ → Nf Γ A → Sub Γ (Δ , A)

-- mutual
--   _∘ˢ_ : ∀ {Γ Δ Ξ} → Sub Γ Δ → Sub Ξ Γ → Sub Ξ Δ
--   ε       ∘ˢ s' = ε
--   (s , x) ∘ˢ s' = (s ∘ˢ s') , (sub s' x)
  
--   η : ∀ {Γ A} → A ∈ Γ → Nf Γ A
--   η = {!!}

--   topˢ : ∀ {Γ A} → Sub (Γ , A) Γ
--   topˢ {ε}         = ε
--   topˢ {Γ , B} {A} = {!topˢ {Γ , B}!} , (η (vs vz))

--   keepˢ : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
--   keepˢ s = {!!} , (η vz)

--   idˢ : ∀ {Γ} → Sub Γ Γ
--   idˢ {ε}     = ε
--   idˢ {Γ , x} = {!idˢ {Γ}!} , η vz
  
--   sub : ∀ {Γ Δ A} → Sub Γ Δ → Nf Δ A → Nf Γ A
--   sub s (λ' A t)      = λ' A (sub {!!} t)
--   sub s (ne (v , sp)) = {!!}


-- Renamings
--------------------------------------------------------------------------------

-- Ren Sub : Con → Con → Set
-- Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
-- Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Tm Δ τ

-- Shub : Con → Con → Set
-- Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

-- _//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Tm Γ τ → Tm Δ τ
-- θ // var v = θ [] v
-- θ // λ' t = λ' ((θ ∘ (_ ∷_)) // t)
-- θ // (f ∙ x) = (θ // f) ∙ (θ // x)

-- wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
-- wkr r here    = here
-- wkr r (there i) = there (r i)

-- ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
-- ren r []      = var ∘ r
-- ren r (_ ∷ Ξ) = ren (wkr r) Ξ

-- wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
-- wks s here    = var here
-- wks s (there i) = ren there // s i

-- sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
-- sub s []      = s
-- sub s (_ ∷ Ξ) = sub (wks s) Ξ

-- weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
-- weak []      = id
-- weak (_ ∷ Ξ) = weak Ξ ∘ there

-- shiftTm : ∀ {Γ A} Ξ → Tm Γ A → Tm (Γ <>< Ξ) A
-- shiftTm Ξ = ren (weak Ξ) //_


-- OPE
--------------------------------------------------------------------------------

-- data _⊆_ : Con → Con → Set where
--   stop : ∀ {Γ} → Γ ⊆ Γ
--   skip : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ⊆ (Δ , A)
--   keep : ∀ {Γ Δ A} → Γ ⊆ Δ → (Γ , A) ⊆ (Δ , A)

-- trans-⊆ : ∀ {Γ Δ θ} → Γ ⊆ Δ → Δ ⊆ θ → Γ ⊆ θ
-- trans-⊆ stop q = q
-- trans-⊆ p stop = p
-- trans-⊆ (skip p) (skip q) = skip (trans-⊆ (skip p) q)
-- trans-⊆ (skip p) (keep q) = skip (trans-⊆ p q)
-- trans-⊆ (keep p) (skip q) = skip (trans-⊆ (keep p) q)
-- trans-⊆ (keep p) (keep q) = keep (trans-⊆ p q)

-- ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
-- ren-∈ stop     v         = v
-- ren-∈ (skip r) v         = there (ren-∈ r v)
-- ren-∈ (keep r) here      = here
-- ren-∈ (keep r) (there v) = there (ren-∈ r v)

-- ren-Tm : ∀ {Γ Δ A} → Γ ⊆ Δ → Tm Γ A → Tm Δ A
-- ren-Tm r (var v) = var (ren-∈ r v)
-- ren-Tm r (λ' t)  = λ' (ren-Tm (keep r) t)
-- ren-Tm r (f ∙ x) = ren-Tm r f ∙ ren-Tm r x

-- shift : ∀ {Γ Δ} xs → Γ ⊆ Δ → (Γ <>< xs) ⊆ (Δ <>< xs)
-- shift []       s = s
-- shift (x ∷ xs) s = shift xs (keep s)

-- wks : ∀ Γ xs → Γ ⊆ (Γ <>< xs)
-- wks Γ []       = stop
-- wks Γ (x ∷ xs) = trans-⊆ (skip stop) (wks (Γ , x) xs)


-- data Ix : Con → Set where
--   here  : ∀ {Γ} → Ix Γ
--   there : ∀ {Γ A} → Ix Γ → Ix (Γ , A)

-- ins : ∀ Γ → Ix Γ → Ty → Con
-- ins Γ       here      A = Γ , A
-- ins (Γ , B) (there i) A = ins Γ i A , B

-- ins-⊆ : ∀ Γ A i → Γ ⊆ ins Γ i A
-- ins-⊆ Γ       A here      = skip stop
-- ins-⊆ (Γ , _) A (there i) = keep (ins-⊆ Γ A i)

-- wk : ∀ Γ A → Γ ⊆ (Γ , A)
-- wk = λ Γ A → skip stop

-- comm-∈ :
--   ∀ {Γ A B C i}(v : C ∈ Γ)
--   → ren-∈ (wk _ B) (ren-∈ (ins-⊆ Γ A i) v)
--   ≡ ren-∈ (keep (ins-⊆ _ A i)) (ren-∈ (wk Γ B) v)
-- comm-∈ v = refl

-- -- comm-Tm :
-- --   ∀ {Γ A B C i}(t : Tm Γ C)
-- --   → ren-Tm (wk _ B) (ren-Tm (ins-⊆ Γ A i) t)
-- --   ≡ ren-Tm (keep (ins-⊆ _ A i)) (ren-Tm (wk Γ B) t)
-- -- comm-Tm (var x) = refl
-- -- comm-Tm {Γ}{A}{B}{C ⇒ D}{i}(λ' t) = cong λ' {!comm-Tm {Γ , C}{A}{B}{D}{there i} t!}
-- -- comm-Tm (f ∙ x) = cong₂ _∙_ (comm-Tm f) (comm-Tm x)

-- <><-snoc : ∀ Γ xs A → (Γ <>< xs , A) ≡ (Γ <>< (xs ++ A ∷ []))
-- <><-snoc Γ []       A = refl
-- <><-snoc Γ (x ∷ xs) A = <><-snoc (Γ , x) xs A



-- comm-Tm' :
--   ∀ Γ A B C i xs (t : Tm Γ C)
--   → ren-Tm (shift xs (wk _ B))             (ren-Tm (shift xs (ins-⊆ Γ A i)) t)
--   ≡ ren-Tm (shift xs (keep (ins-⊆ _ A i))) (ren-Tm (shift xs (wk Γ B)) t)
-- comm-Tm' = ?
  
-- -- comm-Tm' Γ A B C i xs (var x)  = {!!}
-- -- comm-Tm' Γ A B (C ⇒ D) i xs (λ' t) with subst (λ x → Tm x D) (<><-snoc Γ xs C) t
-- -- ... | t' = {!comm-Tm' Γ A B D i (xs ++ C ∷ []) t'!}
-- -- comm-Tm' Γ A B C i xs (t ∙ t₁) = {!!}


-- -- lem : ∀ {Γ Δ} (p : Γ ⊆ Δ) → trans-⊆ p stop ≡ p
-- -- lem stop = refl
-- -- lem (skip p) = refl
-- -- lem (keep p) = refl

-- -- ren-∈-∘ : ∀ {Γ Δ θ A}(p : Γ ⊆ Δ)(q : Δ ⊆ θ)(v : A ∈ Γ) → ren-∈ q (ren-∈ p v) ≡ ren-∈ (trans-⊆ p q) v
-- -- ren-∈-∘ stop q v = refl
-- -- ren-∈-∘ p stop here      rewrite lem p = refl
-- -- ren-∈-∘ p stop (there v) rewrite lem p = refl
-- -- ren-∈-∘ (skip p) (skip q) v = cong there {!!}
-- -- ren-∈-∘ (skip p) (keep q) v = cong there {!!}
-- -- ren-∈-∘ (keep p) (skip q) v = cong there {!!}
-- -- ren-∈-∘ (keep p) (keep q) v = {!!}

