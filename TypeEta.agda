
module SystemFOmega.TypeEta where

open import SystemFOmega.Type
open import SystemFOmega.TypeProofs

open import Data.Sum
open import Relation.Binary.PropositionalEquality

ηᶜ : ∀ {Γ A} → A ∈ Γ → Con
ηᶜ {Γ ▷ A} vz     = Γ ▷ A ▷ A
ηᶜ {Γ ▷ B} (vs v) = ηᶜ v ▷ B

⊆-η : ∀ {Γ A}(v : A ∈ Γ) → Γ ⊆ ηᶜ v
⊆-η vz     = keep (add refl)
⊆-η (vs v) = keep (⊆-η v)

η-∈ : ∀ {Γ A}(v : A ∈ Γ) → A ∈ drop (ren-∈ (⊆-η v) v)
η-∈ vz     = vz
η-∈ (vs v) = η-∈ v

un-η : ∀ {Γ A}(v : A ∈ Γ) → Γ ⊆ subᶜ (ren-∈ (⊆-η v) v)
un-η vz     = refl
un-η (vs v) = keep (un-η v)

-- todo : use _++_ instead of snocSp
infixr 5 _++_
_++_ : ∀ {Γ A B C} → Sp Γ A B → Sp Γ B C → Sp Γ A C
_++_ ε        ys = ys
_++_ (x ∷ xs) ys = x ∷ xs ++ ys

++-ε : ∀ {Γ A B} (sp : Sp Γ A B) → sp ++ ε ≡ sp
++-ε ε        = refl
++-ε (x ∷ sp) = cong (x ∷_) (++-ε sp)

sub-η-Ne :
  ∀ {Γ A B}(v : A ∈ Γ) (v' : B ∈ subᶜ v) t' sp
  → sub v t' (η-Ne (ren-∈ (subᶜ-⊆ v) v' , sp)) ≡ ne (v' , subSp v t' sp)
sub-η-Ne v v' t sp with ∈-eq v (ren-∈ (subᶜ-⊆ v) v')
sub-η-Ne v v' t sp | inj₁ refl = {!!}
sub-η-Ne v v' t sp | inj₂ y    = {!!}

mutual
  η-≡ :
    ∀ {Γ A B}(v : A ∈ Γ)(t : Ty Γ B)
    → sub (ren-∈ (⊆-η v) v) (η (η-∈ v)) (ren (⊆-η v) t) ≡ ren (un-η v) t
  η-≡ v (A ⇒ B)        = cong₂ _⇒_ (η-≡ v A) (η-≡ v B)
  η-≡ v (ƛ t)          = cong ƛ_  (η-≡ (vs v) t)
  η-≡ v (∀' t)         = cong ∀'_ (η-≡ (vs v) t)
  η-≡ v (ne (v' , sp)) with ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v')
  ... | inj₁ refl  rewrite η-≡-Sp v sp = {!ren-∈ (un-η v) v'!}
  ... | inj₂ y    = cong₂ (λ x y → ne (x , y)) {!!} (η-≡-Sp v sp)

  η-≡-Sp :
    ∀ {Γ A B C}(v : A ∈ Γ)(sp : Sp Γ B C)
    → subSp (ren-∈ (⊆-η v) v) (η (η-∈ v)) (renSp (⊆-η v) sp) ≡ renSp (un-η v) sp
  η-≡-Sp v ε        = refl
  η-≡-Sp v (t ∷ sp) = cong₂ _∷_ (η-≡ v t) (η-≡-Sp v sp)

  η-≡-◇ : ∀ {Γ A B}(v : A ∈ Γ)(sp : Sp Γ A B)(sp' : Sp Γ B ⋆) → η-Ne (v , sp) ◇ sp' ≡ ne (v , (sp ++ sp'))
  η-≡-◇ v sp ε         = cong (λ x → ne (v , x)) (sym (++-ε sp))
  η-≡-◇ v sp (x ∷ sp') = {!!}


  -- ne2nfSubst : ∀ {ρ Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (ts : Sp Γ τ ρ) → (u : Nf (Γ - x) σ) → (ne2nf (wkv x y , ts)) [ x := u ] ≡ ne2nf (y , (ts < x := u >))


-- appNfNe2nfConcat : ∀ {Γ σ τ} → (x : Var Γ σ) → (ts : Sp Γ σ τ) → (us : Sp Γ τ ○) → (ne2nf (x , ts)) ◇ us ≡ ne (x , concatSp ts us)

  -- η-≡-◇ : ∀ {Γ A}(v : A ∈ Γ) (sp : Sp Γ A ⋆) → η v ◇ sp ≡ ne (v , sp)
  -- η-≡-◇ v ε        = refl
  -- η-≡-◇ v (t ∷ sp) = {!!}
  -- η-≡-◇ v (t ∷ ε) = {!!}
  -- η-≡-◇ v (t ∷ x ∷ ε) = {!!}
  -- η-≡-◇ v (t ∷ x ∷ x₁ ∷ sp) = {!!}








η-inst : ∀ {Γ A B} (t : Ty (Γ ▷ A) B) → inst (η vz) (ren (keep top) t) ≡ t
η-inst t = trans (η-≡ vz t) (ren-refl t)


