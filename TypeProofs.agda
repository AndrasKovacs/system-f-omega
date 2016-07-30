
module SystemFOmega.TypeProofs where

open import SystemFOmega.Type

open import Data.Empty
open import Data.Product renaming (map to pmap)
open import Data.Sum renaming (map to smap)
open import Data.Unit
open import Function using (_$_; _∋_)
open import Relation.Binary.PropositionalEquality
import Function as F


-- Categorical stuff for _⊆_
--------------------------------------------------------------------------------

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


-- Substituting a newly added variable does nothing
--------------------------------------------------------------------------------

Fresh : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Δ → Set
Fresh refl     v      = ⊥
Fresh (add o)  vz     = ⊤
Fresh (add o)  (vs v) = Fresh o v
Fresh (keep o) vz     = ⊥
Fresh (keep o) (vs v) = Fresh o v

Fresh-sub-⊆ : ∀ {Γ Δ A v} o → Fresh {Γ}{Δ}{A} o v → Γ ⊆ subᶜ v
Fresh-sub-⊆ {v = vz}   refl ()
Fresh-sub-⊆ {v = vz}   (add o) p = o
Fresh-sub-⊆ {v = vz}   (keep o) ()
Fresh-sub-⊆ {v = vs v} refl ()
Fresh-sub-⊆ {v = vs v} (add o)  p = add (Fresh-sub-⊆ o p)
Fresh-sub-⊆ {v = vs v} (keep o) p = keep (Fresh-sub-⊆ o p)

fresh-∈-eq :
 ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(v : A ∈ Δ)(v' : B ∈ Γ)(f : Fresh o v)
 → ∈-eq v (ren-∈ o v') ≡ inj₂ (ren-∈ (Fresh-sub-⊆ o f) v')
fresh-∈-eq refl     v      v'      ()
fresh-∈-eq (add o)  vz     v'      p = refl
fresh-∈-eq (add o)  (vs v) v'      p rewrite fresh-∈-eq o v v' p = refl
fresh-∈-eq (keep o) vz     v'      ()
fresh-∈-eq (keep o) (vs v) vz      p = refl
fresh-∈-eq (keep o) (vs v) (vs v') p rewrite fresh-∈-eq o v v' p = refl

mutual
  fresh-sub :
    ∀ {Γ Δ A B} (o : Γ ⊆ Δ) (v : A ∈ Δ)(f : Fresh o v)(t' : Ty (drop v) A)(t : Ty Γ B)
    → sub v t' (ren o t) ≡ ren (Fresh-sub-⊆ o f) t
  fresh-sub o v f t' (A ⇒ B) rewrite fresh-sub o v f t' A | fresh-sub o v f t' B = refl
  fresh-sub o v f t' (ƛ t)  = cong ƛ_ (fresh-sub (keep o) (vs v) f t' t)
  fresh-sub o v f t' (∀' t) = cong ∀'_ (fresh-sub (keep o) (vs v) f t' t)
  fresh-sub o v f t' (ne (v' , sp)) with ∈-eq v (ren-∈ o v') | fresh-∈-eq o v v' f
  ... | inj₁ refl | ()
  ... | inj₂ _    | refl = cong (λ x → ne (_ , x)) (fresh-sub-Sp o v f t' sp)

  fresh-sub-Sp :
    ∀ {Γ Δ A B C} (o : Γ ⊆ Δ) (v : A ∈ Δ)(f : Fresh o v)(t' : Ty (drop v) A)(sp : Sp Γ B C)
    → subSp v t' (renSp o sp) ≡ renSp (Fresh-sub-⊆ o f) sp
  fresh-sub-Sp o v f t' ε        = refl
  fresh-sub-Sp o v f t' (x ∷ sp) = cong₂ _∷_ (fresh-sub o v f t' x) (fresh-sub-Sp o v f t' sp)

inst-top : ∀ {Γ A B} (t' : Ty Γ A)(t : Ty Γ B) → inst t' (ren top t) ≡ t
inst-top t' t = trans (fresh-sub top vz _ t' t) (ren-refl t)

inst-top-Sp : ∀ {Γ A B C} (t' : Ty Γ A)(sp : Sp Γ B C) → subSp vz t' (renSp top sp) ≡ sp
inst-top-Sp t' sp = trans (fresh-sub-Sp top vz _ t' sp) (renSp-refl sp)

-- Top commutes with any embedding
--------------------------------------------------------------------------------

top-comm :
  ∀ {Γ Δ A B}(t : Ty Γ A)(o : Γ ⊆ Δ) → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-comm {B = B} t o rewrite ren-∘ (top{B}) o t | ren-∘ (keep o) (top {B}) t | ∘-refl o = refl

top-comm-Sp :
  ∀ {Γ Δ A B C}(sp : Sp Γ A B)(o : Γ ⊆ Δ)
  → renSp top (renSp o sp) ≡ renSp (keep o) (renSp (top {C}) sp)
top-comm-Sp {C = C} sp o rewrite
  renSp-∘ (top{C}) o sp | renSp-∘ (keep o) (top {C}) sp | ∘-refl o = refl

-- Renaming commutes with substitution
--------------------------------------------------------------------------------

ren-sub-∈ :
  ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (v : A ∈ Γ) (v' : B ∈ Γ)
  → ∈-eq (ren-∈ o v) (ren-∈ o v') ≡ smap F.id (ren-∈ (⊆-subᶜ v o)) (∈-eq v v')
ren-sub-∈ refl v v' with ∈-eq v v'
... | inj₁ _ = refl
... | inj₂ _ = refl
ren-sub-∈ (add o)  v v' with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ _ | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ _ | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) (vs v) (vs v') with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) vz vz      = refl
ren-sub-∈ (keep o) vz (vs v') = refl
ren-sub-∈ (keep o) (vs v) vz  = refl

ren-drop-sub' :
  ∀ {Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)
  → (⊆-subᶜ v o ∘ drop-sub-⊆ v) ≡ (drop-sub-⊆ (ren-∈ o v) ∘ ⊆-drop v o)
ren-drop-sub' refl     v      = sym (∘-refl (drop-sub-⊆ v))
ren-drop-sub' (add o)  v      = cong add (ren-drop-sub' o v)
ren-drop-sub' (keep o) vz     = ∘-refl o
ren-drop-sub' (keep o) (vs v) = cong add (ren-drop-sub' o v)

ren-drop-sub :
  ∀ {Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)(t : Ty (drop v) A)
  → ren (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t) ≡ ren (drop-sub-⊆ (ren-∈ o v)) (ren (⊆-drop v o) t)
ren-drop-sub o v t rewrite
  ren-∘ (⊆-subᶜ v o) (drop-sub-⊆ v) t | ren-∘ (drop-sub-⊆ (ren-∈ o v)) (⊆-drop v o) t
  = cong (λ x → ren x t) (ren-drop-sub' o v)

mutual
  ren-sub :
    ∀ {Γ Δ A B} (v : A ∈ Γ) (o : Γ ⊆ Δ) t' (t : Ty Γ B)
    → ren (⊆-subᶜ v o) (sub v t' t) ≡ sub (ren-∈ o v) (ren (⊆-drop v o) t') (ren o t)
  ren-sub v o t' (A ⇒ B) rewrite ren-sub v o t' A | ren-sub v o t' B = refl
  ren-sub v o t' (ƛ t)  = cong ƛ_  (ren-sub (vs v) (keep o) t' t)
  ren-sub v o t' (∀' t) = cong ∀'_ (ren-sub (vs v) (keep o) t' t)
  ren-sub v o t' (ne (v' , sp))
    with ∈-eq (ren-∈ o v) (ren-∈ o v') | ∈-eq v v' | ren-sub-∈ o v v'
  ... | inj₁ refl | inj₁ _    | refl
      rewrite
        sym $ ren-sub-Sp v o t' sp
      | ren-◇ (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t') (subSp v t' sp)
      | ren-drop-sub o v t'
      = refl
  ... | inj₂ _    | inj₂ v''  | refl rewrite ren-sub-Sp v o t' sp = refl
  ... | inj₁ refl | inj₂ _    | ()
  ... | inj₂ _    | inj₁ refl | ()

  ren-sub-Sp :
    ∀ {Γ Δ A B C} (v : A ∈ Γ) (o : Γ ⊆ Δ) t' (sp : Sp Γ B C) →
    renSp (⊆-subᶜ v o) (subSp v t' sp) ≡ subSp (ren-∈ o v) (ren (⊆-drop v o) t') (renSp o sp)
  ren-sub-Sp v o t' ε        = refl
  ren-sub-Sp v o t' (x ∷ sp) = cong₂ _∷_ (ren-sub v o t' x) (ren-sub-Sp v o t' sp)

  ren-◇ :
    ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (t : Ty Γ A) (sp : Sp Γ A B) →
    ren o (t ◇ sp) ≡ ren o t ◇ renSp o sp
  ren-◇ o t     ε        = refl
  ren-◇ o (ƛ t) (x ∷ sp) rewrite
    ren-◇ o (inst x t) sp | ren-sub vz (keep o) x t = refl

ren-top-sub :
  ∀ {Γ A B C}(v : A ∈ Γ) (t' : Ty (drop v) A) (t : Ty Γ B)
  → ren (top {C}) (sub v t' t) ≡ sub (vs v) t' (ren (top {C}) t)
ren-top-sub {C = C} v t' t rewrite ren-sub v (top {C}) t' t | ren-refl t' = refl

-- Substitution commutes with substitution
--------------------------------------------------------------------------------

drop-drop-sub :
  ∀ {Γ A B}(v : A ∈ Γ){v' : B ∈ drop v} → drop v' ⊆ drop (ren-∈ (drop-sub-⊆ v) v')
drop-drop-sub v {v'} = ⊆-drop v' (drop-sub-⊆ v)

drop-drop : ∀ {Γ A B}(v : A ∈ Γ){v' : B ∈ drop v} → drop v' ⊆ drop (ren-∈ (drop-⊆ v) v')
drop-drop v {v'} = ⊆-drop v' (drop-⊆ v)

_-_ : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v) → A ∈ subᶜ (ren-∈ (drop-⊆ v) v')
_-_ vz     v' = vz
_-_ (vs v) v' = vs (v - v')

sub-drop- : ∀ {Γ A B}(v : A ∈ Γ){v' : B ∈ drop v} → subᶜ v' ⊆ drop (v - v')
sub-drop- vz     = refl
sub-drop- (vs v) = sub-drop- v

exc : ∀ {Γ A B}(v : A ∈ Γ){v' : B ∈ drop v} → subᶜ (v - v') ⊆ subᶜ (ren-∈ (drop-sub-⊆ v) v')
exc vz     = refl
exc (vs v) = keep (exc v)

remove- :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → (exc v ∘ drop-sub-⊆ (v - v') ∘ sub-drop- v) ≡ ⊆-subᶜ v' (drop-sub-⊆ v)
remove- vz     v' = refl
remove- (vs v) v' = cong add (remove- v v')

Fresh- :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → Fresh (drop-sub-⊆ (ren-∈ (drop-⊆ v) v') ∘ ⊆-drop v' (drop-⊆ v)) (v - v')
Fresh- vz     v' = tt
Fresh- (vs v) v' = Fresh- v v'

remove-Fresh- :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → (exc v ∘ Fresh-sub-⊆
       (drop-sub-⊆ (ren-∈ (drop-⊆ v) v') ∘ ⊆-drop v' (drop-⊆ v))
       (Fresh- v v'))
  ≡ (drop-sub-⊆ (ren-∈ (drop-sub-⊆ v) v') ∘ ⊆-drop v' (drop-sub-⊆ v))
remove-Fresh- vz     v' = refl
remove-Fresh- (vs v) v' = cong add (remove-Fresh- v v')

sub-sub-∈ :
  ∀ {Γ A B C}(v : A ∈ Γ)(v₁ : B ∈ Γ)(v₂ : C ∈ drop v₁)

  → (∃₂ λ p v''
     → ∈-eq v₁ v ≡ inj₁ p
     × ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v ≡ inj₂ v''
     × ∈-eq (v₁ - v₂) v'' ≡ inj₁ p)
  ⊎
    (∃₂ λ p v'
     → ∈-eq v₁ v ≡ inj₂ v'
     × ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v ≡ inj₁ p
     × ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v' ≡ inj₁ p)
  ⊎
    (∃₂ λ v' v'' → ∃₂ λ w' w''
     → ∈-eq v₁ v ≡ inj₂ v'
     × ∈-eq (v₁ - v₂) v'' ≡ inj₂ w'
     × ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v ≡ inj₂ v''
     × ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v' ≡ inj₂ w''
     × w'' ≡ ren-∈ (exc v₁) w')

sub-sub-∈ vz          vz           _       = inj₁ (refl , vz , refl , refl , refl)
sub-sub-∈ vz          (vs vz)      vz      = inj₂ (inj₂ (vz , vz , vz , vz , refl , refl , refl , refl , refl))
sub-sub-∈ vz          (vs vz)      (vs v₂) = inj₂ (inj₂ (vz , vz , vz , vz , refl , refl , refl , refl , refl))
sub-sub-∈ vz          (vs (vs v₁)) v₂      = inj₂ (inj₂ (vz , vz , vz , vz , refl , refl , refl , refl , refl))
sub-sub-∈ (vs vz)     vz           vz      = inj₂ (inj₁ (refl , vz , refl , refl , refl))
sub-sub-∈ (vs (vs v)) vz           vz      = inj₂ (inj₂ ((vs v) , (vs v) , v , v , refl , refl , refl , refl , refl))
sub-sub-∈ (vs v) vz (vs v₂) with sub-sub-∈ v vz v₂
... | inj₁ (p , v'' , a , b , c)
  = inj₂ (inj₂ (v , (vs v'') , v'' , v'' , refl , refl , vs-∈-≡ b , b , refl))
... | inj₂ (inj₁ (p , v' , a , b , c))
  = inj₂ (inj₁ (p , v , refl , vs-∈-≡ b , b ))
... | inj₂ (inj₂ (v' , v'' , w' , w'' , a , b , c , d))
  = inj₂ (inj₂ (v , (vs v'') , v'' , v'' , refl , refl , vs-∈-≡ c , c , refl))
sub-sub-∈ (vs v) (vs v₁) v₂ with sub-sub-∈ v v₁ v₂
... | inj₁ (p , v'' , a , b , c)
  = inj₁ (p , (vs v'') , vs-∈-≡ a , vs-∈-≡ b , vs-∈-≡ c)
... | inj₂ (inj₁ (p , v' , a , b , c))
  = inj₂ (inj₁ (p , (vs v') , vs-∈-≡ a , vs-∈-≡ b , vs-∈-≡ c))
... | inj₂ (inj₂ (v' , v'' , w' , w'' , a , b , c , d , e))
  = inj₂ (inj₂ ((vs v') , (vs v'') , (vs w') , (vs w'') , vs-∈-≡ a , vs-∈-≡ b , vs-∈-≡ c , vs-∈-≡ d , cong vs_ e))

mutual
  sub-sub :
    ∀ {Γ A B C}
      (v₁ : A ∈ Γ)(v₂ : B ∈ drop v₁)
      (t₁ : Ty (drop v₁) A)(t₂ : Ty (drop v₂) B)
      (t  : Ty Γ C)
    → sub (ren-∈ (drop-sub-⊆ v₁) v₂) (ren (drop-drop-sub v₁) t₂) (sub v₁ t₁ t)
    ≡
      ren (exc v₁) (sub (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
      (sub (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) t))

  sub-sub v₁ v₂ t₁ t₂ (A ⇒ B) = cong₂ _⇒_ (sub-sub v₁ v₂ t₁ t₂ A) (sub-sub v₁ v₂ t₁ t₂ B)
  sub-sub v₁ v₂ t₁ t₂ (ƛ  t)  = cong ƛ_  (sub-sub (vs v₁) v₂ t₁ t₂ t )
  sub-sub v₁ v₂ t₁ t₂ (∀' t)  = cong ∀'_ (sub-sub (vs v₁) v₂ t₁ t₂ t)

  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp))
    with sub-sub-∈ v v₁ v₂

  -- Substitute t₁
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ _
    with ∈-eq v₁ v | ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (_ , _ , _  , () , _)           | inj₁ _    | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (_ , _ , _  , () , _)           | inj₂ _    | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (_ , _ , () , _  , _)           | inj₂ _    | inj₂ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (.refl , v'' , refl , refl , _) | inj₁ refl | inj₂ _
    with ∈-eq (v₁ - v₂) v''
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (.refl , _   , refl , refl , ())   | inj₁ refl | inj₂ _ | inj₂ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ (.refl , v'' , refl , refl , refl) | inj₁ refl | inj₂ _ | inj₁ refl
    rewrite
      ren-∘ (drop-sub-⊆ (v₁ - v₂)) (sub-drop- v₁) (sub v₂ t₂ t₁)
    | ren-◇
        (exc v₁)
        (ren (drop-sub-⊆ (v₁ - v₂) ∘ sub-drop- v₁) (sub v₂ t₂ t₁))
        (subSp (v₁ - v₂)
          (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
          (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) sp))
    | ren-∘ (exc v₁) (drop-sub-⊆ (v₁ - v₂) ∘ sub-drop- v₁)(sub v₂ t₂ t₁)
    | remove- v₁ v₂
    | sym $ sub-sub-Sp v₁ v₂ t₁ t₂ sp
    | sub-◇
         (ren-∈ (drop-sub-⊆ v₁) v₂)
         (ren (⊆-drop v₂ (drop-sub-⊆ v₁)) t₂)
         (ren (drop-sub-⊆ v₁) t₁)
         (subSp v₁ t₁ sp)
    | sym $ ren-sub v₂ (drop-sub-⊆ v₁) t₂ t₁
    = refl

  -- Substitute t₂
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ _)
    with ∈-eq v₁ v
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , _  , ()   , _ , _)) | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , v' , refl , _ , _)) | inj₂ _
    with ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v'
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , _  , refl , _ , ())) | inj₂ _ | inj₂ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , _  , refl , _ , _ )) | inj₂ _ | inj₁ refl
    with ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , _  , refl , () , _)) | inj₂ _ | inj₁ refl | inj₂ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₁ (_ , v' , refl , _  , _)) | inj₂ _ | inj₁ refl | inj₁ refl
    rewrite
      ren-∘ (drop-sub-⊆ (ren-∈ (drop-sub-⊆ v₁) v₂))
            (drop-drop-sub v₁) t₂
    | ren-∘ (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂))
            (⊆-drop v₂ (drop-⊆ v₁)) t₂
    | sub-◇
        (v₁ - v₂)
        (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
        (ren (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁)) t₂)
        (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (⊆-drop v₂ (drop-⊆ v₁)) t₂) sp)
    | ren-◇
        (exc v₁)
        (sub (v₁ - v₂)
             (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
             (ren (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁)) t₂))
        (subSp (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
          (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (⊆-drop v₂ (drop-⊆ v₁)) t₂) sp))
    | sym $ sub-sub-Sp v₁ v₂ t₁ t₂ sp
    | fresh-sub
         (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁))
         (v₁ - v₂)
         (Fresh- v₁ v₂)
         (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
         t₂
    | ren-∘
         (exc v₁)
         (Fresh-sub-⊆
           (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁))
           (Fresh- v₁ v₂))
         t₂
    | remove-Fresh- v₁ v₂
    = refl

  -- Substitute nothing
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ _)
    with ∈-eq v₁ v
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_  , _ , _ , _ , ()   , _ , _ , _ , _)) | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (v' , _ , _ , _ , refl , _ , _ , _ , _)) | inj₂ _
    with ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v'
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_ , _ , _ , _ , refl , _ , _ , () , _)) | inj₂ _ | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_ , _ , _ , _ , refl , _ , _ , _  , _)) | inj₂ _ | inj₂ _
    with ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_  , _   , _ , _ , refl , _ , ()   , _ , _)) | inj₂ _ | inj₂ _  | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (v' , v'' , _ , _ , refl , _ , refl , _ , _)) | inj₂ _ | inj₂ _ | inj₂ _
    with ∈-eq (v₁ - v₂) v''
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_ , _ , _ , _ , refl , ()   , refl , _    , _   )) | inj₂ _ | inj₂ _ | inj₂ _ | inj₁ _
  sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ (inj₂ (_ , _ , _ , _ , refl , refl , refl , refl , refl)) | inj₂ _ | inj₂ _ | inj₂ _ | inj₂ _
    = cong (λ x → ne (_ , x)) (sub-sub-Sp v₁ v₂ t₁ t₂ sp)

  sub-sub-Sp :
    ∀ {Γ A B C D}
      (v₁ : A ∈ Γ)(v₂ : B ∈ drop v₁)
      (t₁ : Ty (drop v₁) A)(t₂ : Ty (drop v₂) B)
      (sp : Sp Γ C D)
    → subSp (ren-∈ (drop-sub-⊆ v₁) v₂) (ren (drop-drop-sub v₁) t₂) (subSp v₁ t₁ sp)
    ≡ renSp (exc v₁) (subSp (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
      (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) sp))

  sub-sub-Sp v₁ v₂ t₁ t₂ ε        = refl
  sub-sub-Sp v₁ v₂ t₁ t₂ (t ∷ sp) =
    cong₂ _∷_ (sub-sub v₁ v₂ t₁ t₂ t) (sub-sub-Sp v₁ v₂ t₁ t₂ sp)

  sub-inst :
    ∀ {Γ A B C}(v : A ∈ Γ) t₁ t₂ (t : Ty (Γ ▷ B) C) →
    sub v t₂ (inst t₁ t) ≡ inst (sub v t₂ t₁) (sub (vs v) t₂ t)
  sub-inst v t₁ t₂ t rewrite
      sym $ ren-refl t₂ -- would be nice to rewrite "ren refl" to "id"
    | sub-sub vz v t₁ t₂ t | ren-refl (sub v t₂ t₁) | ren-refl t₂
    | ren-refl (sub vz (sub v t₂ t₁) (sub (vs v) t₂ t))
    = refl

  sub-◇ :
    ∀ {Γ A B C}(v : A ∈ Γ) t' (t : Ty Γ B)(sp : Sp Γ B C)
    → sub v t' (t ◇ sp) ≡ (sub v t' t ◇ subSp v t' sp)
  sub-◇ v t' t ε        = refl
  sub-◇ v t' (ƛ t) (x ∷ sp) rewrite
    sub-◇ v t' (inst x t) sp | sub-inst v x t' t = refl


-- Correctness of eta-expansion
--------------------------------------------------------------------------------

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

∈-neq : ∀ {Γ A B}(v : A ∈ Γ) (v' : B ∈ subᶜ v) → ∈-eq v (ren-∈ (subᶜ-⊆ v) v') ≡ inj₂ v'
∈-neq vz     v'      = refl
∈-neq (vs v) vz      = refl
∈-neq (vs v) (vs v') = cong (smap F.id vs_) (∈-neq v v')

∈-eq-refl : ∀ {Γ A}(v : A ∈ Γ) → ∈-eq v v ≡ inj₁ refl
∈-eq-refl vz     = refl
∈-eq-refl (vs v) = cong (smap F.id vs_) (∈-eq-refl v)

++-ε : ∀ {Γ A B} (sp : Sp Γ A B) → sp ++ ε ≡ sp
++-ε ε        = refl
++-ε (x ∷ sp) = cong (x ∷_) (++-ε sp)

++-assoc :
  ∀ {Γ A B C D}(sp : Sp Γ A B)(sp' : Sp Γ B C)(sp'' : Sp Γ C D)
  → (sp ++ sp') ++ sp'' ≡ sp ++ sp' ++ sp''
++-assoc ε        sp' sp'' = refl
++-assoc (x ∷ sp) sp' sp'' = cong (x ∷_) (++-assoc sp sp' sp'')

renSp-++ :
  ∀ {Γ Δ A B C}(o : Γ ⊆ Δ)(sp : Sp Γ A B)(sp' : Sp Γ B C)
  → renSp o (sp ++ sp') ≡ renSp o sp ++ renSp o sp'
renSp-++ o ε        sp' = refl
renSp-++ o (x ∷ sp) sp' = cong (ren o x ∷_) (renSp-++ o sp sp')

subSp-++ :
  ∀ {Γ A B C D}(v : A ∈ Γ) t' (sp : Sp Γ B C) (sp' : Sp Γ C D)
  → subSp v t' (sp ++ sp') ≡ subSp v t' sp ++ subSp v t' sp'
subSp-++ v t' ε        sp' = refl
subSp-++ v t' (x ∷ sp) sp' = cong (sub v t' x ∷_) (subSp-++ v t' sp sp')

ren-η-Ne :
  ∀ {B Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)(sp : Sp Γ A B)
  → ren o (η-Ne (v , sp)) ≡ η-Ne (ren-∈ o v , renSp o sp)
ren-η-Ne {⋆}     o v sp = refl
ren-η-Ne {A ⇒ B} o v sp
  rewrite
    (ren-η-Ne {B} (keep o) (vs v) (renSp top sp ++ η vz ∷ ε))
  | top-comm-Sp {C = A} sp o
  | renSp-++ (keep o) (renSp (add refl) sp) (η-Ne (vz , ε) ∷ ε)
  | ren-η-Ne (keep {A} o) vz ε
  = refl

sub-η-Ne-neq :
  ∀ {Γ A B C}(v : A ∈ Γ) (v' : B ∈ subᶜ v) t' (sp : Sp Γ B C)
  → sub v t' (η-Ne (ren-∈ (subᶜ-⊆ v) v' , sp)) ≡ η-Ne (v' , subSp v t' sp)
sub-η-Ne-neq {C = ⋆} v v' t' sp rewrite ∈-neq v v' = refl
sub-η-Ne-neq {A = A}{C = B ⇒ C} v v' t' sp
  rewrite
    sub-η-Ne-neq (vs v) (vs v') t' (renSp top sp ++ η vz ∷ ε)
  | subSp-++ (vs v) t' (renSp (add refl) sp) (η-Ne (vz , ε) ∷ ε)
  | subst
      (λ x → subSp (vs v) x (renSp (add refl) sp)
           ≡ renSp (add refl) (subSp v t' sp))
      (ren-refl t')
      (sym (ren-sub-Sp v (add {B} refl) t' sp))
  | sub-η-Ne-neq (vs v) (vz {B}) t' ε
  = refl

◇-++ :
  ∀ {Γ A B C} (t : Ty Γ A)(sp : Sp Γ A B)(sp' : Sp Γ B C)
  → (t ◇ sp) ◇ sp' ≡ t ◇ (sp ++ sp')
◇-++ t     ε        sp' = refl
◇-++ (ƛ t) (x ∷ sp) sp' = ◇-++ (sub vz x t) sp sp'

η-∈-lem1 :
  ∀ {Γ A}(v v' : A ∈ Γ)
  → ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v') ≡ inj₁ refl
  → ren-∈ (drop-sub-⊆ (ren-∈ (⊆-η v) v)) (η-∈ v) ≡ ren-∈ (un-η v) v'
η-∈-lem1 vz vz p = refl
η-∈-lem1 vz (vs v') ()
η-∈-lem1 (vs v) vz ()
η-∈-lem1 (vs v) (vs v') p with
    ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v')
  | inspect (∈-eq (ren-∈ (⊆-η v) v)) (ren-∈ (⊆-η v) v')
η-∈-lem1 (vs v) (vs v') p | inj₁ refl | [ eq ] = cong vs_ (η-∈-lem1 v v' eq)
η-∈-lem1 (vs v) (vs v') () | inj₂ y | [ eq ]

η-∈-lem2 :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ Γ)(v'' : B ∈ subᶜ (ren-∈ (⊆-η v) v))
  → ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v') ≡ inj₂ v''
  → v'' ≡ ren-∈ (un-η v) v'
η-∈-lem2 vz vz v'' ()
η-∈-lem2 vz (vs v') .(vs v') refl = refl
η-∈-lem2 (vs v) vz .vz refl = refl
η-∈-lem2 (vs v) (vs v') v'' p
  with
    ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v')
  | inspect (∈-eq (ren-∈ (⊆-η v) v)) (ren-∈ (⊆-η v) v')
η-∈-lem2 (vs v) (vs v') v'' () | inj₁ x | [ eq ]
η-∈-lem2 (vs v) (vs v') .(vs y) refl | inj₂ y | [ eq ] = cong vs_ (η-∈-lem2 v v' y eq)

mutual
  η-≡ :
    ∀ {Γ A B}(v : A ∈ Γ)(t : Ty Γ B)
    → sub (ren-∈ (⊆-η v) v) (η (η-∈ v)) (ren (⊆-η v) t) ≡ ren (un-η v) t
  η-≡ v (A ⇒ B)        = cong₂ _⇒_ (η-≡ v A) (η-≡ v B)
  η-≡ v (ƛ t)          = cong ƛ_  (η-≡ (vs v) t)
  η-≡ v (∀' t)         = cong ∀'_ (η-≡ (vs v) t)
  η-≡ v (ne (v' , sp))
    with
      ∈-eq (ren-∈ (⊆-η v) v) (ren-∈ (⊆-η v) v')
    | inspect (∈-eq (ren-∈ (⊆-η v) v)) (ren-∈ (⊆-η v) v')
  ... | inj₁ refl | [ eq ]
    rewrite
      η-≡-Sp v sp
    | ren-η-Ne (drop-sub-⊆ (ren-∈ (⊆-η v) v)) (η-∈ v) ε
    | η-≡-◇ (ren-∈ (drop-sub-⊆ (ren-∈ (⊆-η v) v)) (η-∈ v))
            ε (renSp (un-η v) sp)
    | η-∈-lem1 v v' eq
    = refl
  ... | inj₂ v''  | [ eq ]
    rewrite
      η-≡-Sp v sp
    | η-∈-lem2 v v' v'' eq
    = refl

  η-≡-ƛ : ∀ {Γ A B}(f : Ty Γ (A ⇒ B)) → f ≡ (ƛ (ren top f ◇ (η vz ∷ ε)))
  η-≡-ƛ (ƛ f) = cong ƛ_ (trans (sym (ren-refl f)) (sym (η-≡ vz f)))

  η-≡-Sp :
    ∀ {Γ A B C}(v : A ∈ Γ)(sp : Sp Γ B C)
    → subSp (ren-∈ (⊆-η v) v) (η (η-∈ v)) (renSp (⊆-η v) sp) ≡ renSp (un-η v) sp
  η-≡-Sp v ε        = refl
  η-≡-Sp v (t ∷ sp) = cong₂ _∷_ (η-≡ v t) (η-≡-Sp v sp)

  η-≡-◇ :
    ∀ {Γ A B}(v : A ∈ Γ)(sp : Sp Γ A B)(sp' : Sp Γ B ⋆)
    → η-Ne (v , sp) ◇ sp' ≡ ne (v , (sp ++ sp'))
  η-≡-◇ v sp ε         = cong (λ x → ne (v , x)) (sym (++-ε sp))
  η-≡-◇ v sp (x ∷ sp')
    rewrite
      sub-η-Ne-neq vz v x (renSp top sp ++ η vz ∷ ε)
    | subSp-++ vz x (renSp (add refl) sp) (η-Ne (vz , ε) ∷ ε)
    | inst-top-Sp x sp
    | sub-η-Ne-eq vz x ε
    | ren-refl x
    | η-≡-◇ v (sp ++ x ∷ ε) sp'
    | ++-assoc sp (x ∷ ε) sp'
    = refl

  sub-η-Ne-eq :
    ∀ {B Γ A}(v : A ∈ Γ) t' (sp : Sp Γ A B)
    → sub v t' (η-Ne (v , sp)) ≡ (ren (drop-sub-⊆ v) t' ◇ subSp v t' sp)
  sub-η-Ne-eq {⋆}     v t' sp rewrite ∈-eq-refl v = refl
  sub-η-Ne-eq {A ⇒ B} v t' sp
    rewrite
      sub-η-Ne-eq {B} (vs v) t' (renSp top sp ++ η vz ∷ ε)
    | subSp-++ (vs v) t' (renSp (add refl) sp) (η-Ne (vz , ε) ∷ ε)
    | subst (λ x → subSp (vs v) x (renSp (add refl) sp)
                    ≡ renSp (add refl) (subSp v t' sp))
        (ren-refl t')
        (sym (ren-sub-Sp v (add {A} refl) t' sp))
    | sub-η-Ne-neq (vs v) (vz {A}) t' ε
    | η-≡-ƛ (ren (drop-sub-⊆ v) t' ◇ subSp v t' sp)
    | ren-◇ (top {A}) (ren (drop-sub-⊆ v) t') (subSp v t' sp)
    | ren-∘ (top {A}) (drop-sub-⊆ v) t'
    | ◇-++ (ren (add (drop-sub-⊆ v)) t')
           (renSp (add refl) (subSp v t' sp))
           (η-Ne (vz , ε) ∷ ε)
    = refl

η-inst : ∀ {Γ A B} (t : Ty (Γ ▷ A) B) → inst (η vz) (ren (keep top) t) ≡ t
η-inst t = trans (η-≡ vz t) (ren-refl t)

