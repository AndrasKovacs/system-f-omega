
module SystemFOmega.TypeProofsRenRefl where

open import SystemFOmega.TypeRenRefl

open import Data.Empty
open import Data.Product renaming (map to pmap)
open import Data.Sum renaming (map to smap)
open import Data.Unit
open import Function using (_$_; _∋_)
open import Relation.Binary.PropositionalEquality
import Function as F

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

-- Top commutes with any embedding
--------------------------------------------------------------------------------

top-comm :
  ∀ {Γ Δ A B}(t : Ty Γ A)(o : Γ ⊆ Δ) → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-comm {B = B} t o rewrite ren-∘ (top{B}) o t | ren-∘ (keep o) (top {B}) t | ∘-refl o = refl

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
  ... | inj₁ refl | inj₁ _    | refl rewrite
    sym $ ren-sub-Sp v o t' sp | ren-◇ (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t') (subSp v t' sp)
    = cong (_◇ renSp (⊆-subᶜ v o) (subSp v t' sp)) (ren-drop-sub o v t')
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

-- mutual
--   sub-sub :
--     ∀ {Γ A B C}
--       (v₁ : A ∈ Γ)(v₂ : B ∈ drop v₁)
--       (t₁ : Ty (drop v₁) A)(t₂ : Ty (drop v₂) B)
--       (t  : Ty Γ C)
--     → sub (ren-∈ (drop-sub-⊆ v₁) v₂) (ren (drop-drop-sub v₁) t₂) (sub v₁ t₁ t)
--     ≡
--       ren (exc v₁) (sub (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--       (sub (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) t))
--   sub-sub v₁ v₂ t₁ t₂ (A ⇒ B) = cong₂ _⇒_ (sub-sub v₁ v₂ t₁ t₂ A) (sub-sub v₁ v₂ t₁ t₂ B)
--   sub-sub v₁ v₂ t₁ t₂ (ƛ  t)  = cong ƛ_  (sub-sub (vs v₁) v₂ t₁ t₂ t )
--   sub-sub v₁ v₂ t₁ t₂ (∀' t)  = cong ∀'_ (sub-sub (vs v₁) v₂ t₁ t₂ t)
--   sub-sub v₁ v₂ t₁ t₂ (ne (v , sp))
--     with ∈-eq v₁ v | ∈-eq (ren-∈ (drop-⊆ v₁) v₂) v
--   sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ refl | inj₁ refl = {!!} -- impossible
--   sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₁ refl | inj₂ v''
--     with ∈-eq (v₁ - v₂) v''
--   ... | inj₂ y    = {!!} -- impossible      
--   ... | inj₁ refl
--         rewrite
--         ren-∘ (drop-sub-⊆ (v₁ - v₂)) (sub-drop- v₁) (sub v₂ t₂ t₁)
--       | ren-◇
--           (exc v₁)
--           (ren (drop-sub-⊆ (v₁ - v₂) ∘ sub-drop- v₁) (sub v₂ t₂ t₁))
--           (subSp (v₁ - v₂)
--             (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--             (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) sp))
--       | ren-∘ (exc v₁) (drop-sub-⊆ (v₁ - v₂) ∘ sub-drop- v₁)(sub v₂ t₂ t₁)
--       | remove- v₁ v₂
--       | sym $ sub-sub-Sp v₁ v₂ t₁ t₂ sp
--       | sub-◇
--            (ren-∈ (drop-sub-⊆ v₁) v₂)
--            (ren (⊆-drop v₂ (drop-sub-⊆ v₁)) t₂)
--            (ren (drop-sub-⊆ v₁) t₁)
--            (subSp v₁ t₁ sp)
--       | sym $ ren-sub v₂ (drop-sub-⊆ v₁) t₂ t₁
--       = refl

--   sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ v'   | inj₁ refl
--     with ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v'
--   ... | inj₂ _    = {!!} -- impossible    
--   ... | inj₁ refl
--         rewrite
--         ren-∘ (drop-sub-⊆ (ren-∈ (drop-sub-⊆ v₁) v₂))
--               (drop-drop-sub v₁) t₂
--       | ren-∘ (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂))
--               (⊆-drop v₂ (drop-⊆ v₁)) t₂
--       | sub-◇
--           (v₁ - v₂)
--           (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--           (ren (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁)) t₂)
--           (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (⊆-drop v₂ (drop-⊆ v₁)) t₂) sp)
--       | ren-◇
--           (exc v₁)
--           (sub (v₁ - v₂)
--                (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--                (ren (drop-sub-⊆ (ren-∈ (drop-⊆ v₁) v₂) ∘ ⊆-drop v₂ (drop-⊆ v₁)) t₂))
--           (subSp (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--             (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (⊆-drop v₂ (drop-⊆ v₁)) t₂) sp))
--       | sym $ sub-sub-Sp v₁ v₂ t₁ t₂ sp
--       = {!!}


--   -- fresh-sub :
--   --   ∀ {Γ Δ A B} (o : Γ ⊆ Δ) (v : A ∈ Δ)(f : Fresh o v)(t' : Ty (drop v) A)(t : Ty Γ B)
--   --   → sub v t' (ren o t) ≡ ren (Fresh-sub-⊆ o f) t
    
--   sub-sub v₁ v₂ t₁ t₂ (ne (v , sp)) | inj₂ v'   | inj₂ v'' -- v , v' and v'' are index-equal
--     with ∈-eq (ren-∈ (drop-sub-⊆ v₁) v₂) v' |
--          ∈-eq (v₁ - v₂) v'' -- therefore these must be inj₂ too
--   ... | inj₁ x | inj₁ x₁ = {!!} -- impossible
--   ... | inj₁ x | inj₂ y  = {!!} -- impossible
--   ... | inj₂ y | inj₁ x  = {!!} -- impossible
--   ... | inj₂ w' | inj₂ w'' =
--     cong₂ (λ x y → ne (x , y)) {!!} (sub-sub-Sp v₁ v₂ t₁ t₂ sp)

--   sub-sub-Sp :
--     ∀ {Γ A B C D}
--       (v₁ : A ∈ Γ)(v₂ : B ∈ drop v₁)
--       (t₁ : Ty (drop v₁) A)(t₂ : Ty (drop v₂) B)
--       (sp : Sp Γ C D)
--     → subSp (ren-∈ (drop-sub-⊆ v₁) v₂) (ren (drop-drop-sub v₁) t₂) (subSp v₁ t₁ sp)
--     ≡ renSp (exc v₁) (subSp (v₁ - v₂) (ren (sub-drop- v₁) (sub v₂ t₂ t₁))
--       (subSp (ren-∈ (drop-⊆ v₁) v₂) (ren (drop-drop v₁) t₂) sp))

--   sub-sub-Sp v₁ v₂ t₁ t₂ ε        = refl
--   sub-sub-Sp v₁ v₂ t₁ t₂ (t ∷ sp) =
--     cong₂ _∷_ (sub-sub v₁ v₂ t₁ t₂ t) (sub-sub-Sp v₁ v₂ t₁ t₂ sp)

--   sub-inst :
--     ∀ {Γ A B C}(v : A ∈ Γ) t₁ t₂ (t : Ty (Γ ▷ B) C) →
--     sub v t₂ (inst t₁ t) ≡ inst (sub v t₂ t₁) (sub (vs v) t₂ t)
--   sub-inst v t₁ t₂ t rewrite
--       sym $ ren-refl t₂ -- would be nice to rewrite "ren refl" to "id"
--     | sub-sub vz v t₁ t₂ t | ren-refl (sub v t₂ t₁) | ren-refl t₂
--     | ren-refl (sub vz (sub v t₂ t₁) (sub (vs v) t₂ t))
--     = refl

--   sub-◇ :
--     ∀ {Γ A B C}(v : A ∈ Γ) t' (t : Ty Γ B)(sp : Sp Γ B C)
--     → sub v t' (t ◇ sp) ≡ (sub v t' t ◇ subSp v t' sp)
--   sub-◇ v t' t ε        = refl
--   sub-◇ v t' (ƛ t) (x ∷ sp) rewrite
--     sub-◇ v t' (inst x t) sp | sub-inst v x t' t = refl



