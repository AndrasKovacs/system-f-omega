
module SystemFOmega.TypeProofs where

open import SystemFOmega.Type

open import Data.Empty
open import Data.Product renaming (map to pmap)
open import Data.Sum renaming (map to smap)
open import Data.Unit
open import Function using (_$_; _∋_)
open import Relation.Binary.PropositionalEquality

import Function as F
import Relation.Binary.HeterogeneousEquality as H

-- Substituting for a newly added variable does nothing
--------------------------------------------------------------------------------

Fresh : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Δ → Set
Fresh stop ()
Fresh (add o)  vz     = ⊤
Fresh (add o)  (vs v) = Fresh o v
Fresh (keep o) vz     = ⊥
Fresh (keep o) (vs v) = Fresh o v

Fresh-sub-⊆ : ∀ {Γ Δ A v} o → Fresh {Γ}{Δ}{A} o v → Γ ⊆ subᶜ v
Fresh-sub-⊆ {v = vz}   (add o)  f = o
Fresh-sub-⊆ {v = vz}   (keep o) ()
Fresh-sub-⊆ {v = vs v} (add o)  f = add (Fresh-sub-⊆ o f)
Fresh-sub-⊆ {v = vs v} (keep o) f = keep (Fresh-sub-⊆ o f)

fresh-∈-eq :
 ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(v : A ∈ Δ)(v' : B ∈ Γ)(f : Fresh o v)
 → ∈-eq v (ren-∈ o v') ≡ inj₂ (ren-∈ (Fresh-sub-⊆ o f) v')
fresh-∈-eq stop     ()     v' f
fresh-∈-eq (keep o) vz     v' ()
fresh-∈-eq (add o)  vz     v' f = refl
fresh-∈-eq (keep o) (vs v) vz f = refl
fresh-∈-eq (add o)  (vs v) v'      f rewrite fresh-∈-eq o v v' f = refl
fresh-∈-eq (keep o) (vs v) (vs v') f rewrite fresh-∈-eq o v v' f = refl

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
inst-top t' t = trans (fresh-sub top vz _ t' t) (ren-id t)

-- Simple renaming commutations
--------------------------------------------------------------------------------

top-add : ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(t : Ty Γ A) → ren (top {B}) (ren o t) ≡ ren (add o) t
top-add {B = B} o t rewrite ren-∘ (top{B}) o t | id-∘ o = refl

top-keep :
  ∀ {Γ Δ A B}(t : Ty Γ A)(o : Γ ⊆ Δ) → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-keep {B = B} t o rewrite
  ren-∘ (top{B}) o t | ren-∘ (keep o) (top {B}) t | id-∘ o | ∘-id o = refl

-- Renaming commutes with substitution
--------------------------------------------------------------------------------

ren-sub-∈ :
  ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (v : A ∈ Γ) (v' : B ∈ Γ)
  → ∈-eq (ren-∈ o v) (ren-∈ o v') ≡ smap F.id (ren-∈ (⊆-subᶜ v o)) (∈-eq v v')
ren-sub-∈ stop () v'
ren-sub-∈ (add o) v v' with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) (vs v) (vs v') with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) vz    vz      = refl
ren-sub-∈ (keep o) vz    (vs v') = refl
ren-sub-∈ (keep o) (vs v) vz     = refl

ren-drop-sub' :
  ∀ {Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)
  → (⊆-subᶜ v o ∘ drop-sub-⊆ v) ≡ (drop-sub-⊆ (ren-∈ o v) ∘ ⊆-drop v o)
ren-drop-sub' stop ()
ren-drop-sub' (add o)  v      = cong add (ren-drop-sub' o v)
ren-drop-sub' (keep o) vz     = trans (∘-id o) (sym (id-∘ o))
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
    sym $ ren-sub-Sp v o t' sp | ren-sub-◇ (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t') (subSp v t' sp)
    = cong (_◇ renSp (⊆-subᶜ v o) (subSp v t' sp)) (ren-drop-sub o v t')
  ... | inj₂ _    | inj₂ v''  | refl rewrite ren-sub-Sp v o t' sp = refl
  ... | inj₁ refl | inj₂ _    | ()
  ... | inj₂ _    | inj₁ refl | ()

  ren-sub-Sp :
    ∀ {Γ Δ A B C} (v : A ∈ Γ) (o : Γ ⊆ Δ) t' (sp : Sp Γ B C) →
    renSp (⊆-subᶜ v o) (subSp v t' sp) ≡ subSp (ren-∈ o v) (ren (⊆-drop v o) t') (renSp o sp)
  ren-sub-Sp v o t' ε        = refl
  ren-sub-Sp v o t' (x ∷ sp) = cong₂ _∷_ (ren-sub v o t' x) (ren-sub-Sp v o t' sp)

  ren-sub-◇ :
    ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (t : Ty Γ A) (sp : Sp Γ A B) →
    ren o (t ◇ sp) ≡ ren o t ◇ renSp o sp
  ren-sub-◇ o t     ε        = refl
  ren-sub-◇ o (ƛ t) (x ∷ sp) rewrite
    ren-sub-◇ o (inst x t) sp | ren-sub vz (keep o) x t = refl

-- Renaming by top commutes with substitution
--------------------------------------------------------------------------------

ixcong :
  ∀ {I : Set}{A : I → Set}(B : ∀ {i} → A i → Set){i i'}{x : A i}{y : A i'}
  → i ≡ i'
  → (f : ∀ {i} (a : A i) → B a) → x H.≅ y → f x H.≅ f y
ixcong B refl f H.refl = H.refl

⊆-subᶜ-id : ∀ {Γ A} (v : A ∈ Γ) → ⊆-subᶜ v id H.≅ id {subᶜ v}
⊆-subᶜ-id {Γ ▷ A} vz     = H.refl
⊆-subᶜ-id {Γ ▷ A} (vs v) =
  ixcong (λ {x} _ → (subᶜ v ▷ A) ⊆ (subᶜ x ▷ A)) (ren-∈-id v) keep (⊆-subᶜ-id v)

⊆-drop-id : ∀ {Γ A}(v : A ∈ Γ) → ⊆-drop v id H.≅ id {drop v}
⊆-drop-id vz     = H.refl
⊆-drop-id (vs v) = ⊆-drop-id v

ren-top-sub :
  ∀ {Γ A B C}(v : A ∈ Γ) (t' : Ty (drop v) A) (t : Ty Γ B)
  → ren (top {C}) (sub v t' t) ≡ sub (vs v) t' (ren (top {C}) t)
ren-top-sub {Γ}{A}{B}{C} v t' t = H.≅-to-≡
  (H.trans
    (ixcong
      (λ {x} _ → Ty (subᶜ x ▷ C) B)
      (sym $ ren-∈-id v)
      (λ r → ren (add r) (sub v t' t))
      (H.sym (⊆-subᶜ-id v)))
    (H.trans
      (H.≡-to-≅ (ren-sub v top t' t))
      (H.trans
        (ixcong
          (λ {x} _ → Ty (subᶜ x ▷ C) B)
          (ren-∈-id v)
          (λ {x} r → sub (vs x) (ren r t') (ren top t))
          (⊆-drop-id v))
        (H.cong
          (λ x → sub (vs v) x (ren top t))
          (H.≡-to-≅ (ren-id t'))))))

-- Substitution commutes with substitution
--------------------------------------------------------------------------------

-- T.sub v t' (T.sub vz k .B) ≡
-- T.sub vz (T.sub v t' k) (T.sub (vs v) t' .B)

-- sub-∈ : ∀ {Γ A B} (v : A ∈ Γ)(v' : B ∈ subᶜ v) → A ∈ subᶜ (ren-∈ (subᶜ-⊆ v) v')
-- sub-∈ vz     v'      = vz
-- sub-∈ (vs v) vz      = v
-- sub-∈ (vs v) (vs v') = vs sub-∈ v v'

-- exc : ∀ {Γ A B} (v : A ∈ Γ)(v' : B ∈ subᶜ v) → subᶜ (sub-∈ v v') ≡ subᶜ v'
-- exc vz     v'      = cong subᶜ (ren-∈-id v')
-- exc (vs v) vz      = refl
-- exc (vs v) (vs v') = cong (_▷ _) (exc v v')

-- exc→ : ∀ {Γ A B C} (v : A ∈ Γ)(v' : B ∈ subᶜ v) → Ty (subᶜ (sub-∈ v v')) C → Ty (subᶜ v') C
-- exc→ v v' = subst (λ x → Ty x _) (exc v v')

-- exc← : ∀ {Γ A B C} (v : A ∈ Γ)(v' : B ∈ subᶜ v) → Ty (subᶜ v') C → Ty (subᶜ (sub-∈ v v')) C
-- exc← v v' = subst (λ x → Ty x _) (sym $ exc v v')




drop-drop-sub :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → drop (ren-∈ (drop-sub-⊆ v) v') ≡ drop v'
drop-drop-sub vz     v' = cong drop (ren-∈-id v')
drop-drop-sub (vs v) v' = drop-drop-sub v v'

drop-drop-sub← :
  ∀ {Γ A B C}(v : A ∈ Γ){v' : B ∈ drop v}
  → Ty (drop v') C → Ty (drop (ren-∈ (drop-sub-⊆ v) v')) C
drop-drop-sub← v {v'} = subst (λ x → Ty x _) (sym $ drop-drop-sub v v')

drop-drop :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → drop (ren-∈ (drop-⊆ v) v') ≡ drop v'
drop-drop vz     v' = cong drop (ren-∈-id v')
drop-drop (vs v) v' = drop-drop v v'

drop-drop← :
  ∀ {Γ A B C}(v : A ∈ Γ){v' : B ∈ drop v}
  → Ty (drop v') C → Ty (drop (ren-∈ (drop-⊆ v) v')) C
drop-drop← v {v'} = subst (λ x → Ty x _) (sym $ drop-drop v v')

_-_ : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v) → A ∈ subᶜ (ren-∈ (drop-⊆ v) v')
_-_ vz     v' = vz
_-_ (vs v) v' = vs (v - v')

drop- : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v) → drop (v - v') ≡ subᶜ v'
drop- vz     v' = cong subᶜ (ren-∈-id v')
drop- (vs v) v' = drop- v v'

drop-← : ∀ {Γ A B C}(v : A ∈ Γ){v' : B ∈ drop v} → Ty (subᶜ v') C → Ty (drop (v - v')) C
drop-← v {v'} = subst (λ x → Ty x _) (sym $ drop- v v')

exc :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ drop v)
  → subᶜ (ren-∈ (drop-sub-⊆ v) v') ≡ subᶜ (v - v')
exc vz     v' = refl
exc (vs v) v' = cong (_▷ _) (exc v v')

exc← :
  ∀ {Γ A B C}(v : A ∈ Γ){v' : B ∈ drop v}
  → Ty (subᶜ (v - v')) C → Ty (subᶜ (ren-∈ (drop-sub-⊆ v) v')) C
exc← v {v'} = subst (λ x → Ty x _) (sym (exc v v'))

-- commutations for coercion, LOL

sub-inst :
  ∀ {Γ A B C}
    (v₁ : A ∈ Γ)
    (v₂ : B ∈ drop v₁)
    (t₁ : Ty (drop v₁) A)
    (t₂ : Ty (drop v₂) B)
    (t  : Ty Γ C)
  → sub (ren-∈ (drop-sub-⊆ v₁) v₂) (drop-drop-sub← v₁ t₂) (sub v₁ t₁ t)
  ≡ exc← v₁ (sub (v₁ - v₂) (drop-← v₁ (sub v₂ t₂ t₁))
    (sub (ren-∈ (drop-⊆ v₁) v₂) (drop-drop← v₁ t₂) t))
sub-inst v₁ v₂ t₁ t₂ (A ⇒ B) = {!!}

sub-inst v₁ v₂ t₁ t₂ (ƛ t) = {!!}
sub-inst v₁ v₂ t₁ t₂ (∀' t) = {!!}
sub-inst v₁ v₂ t₁ t₂ (ne x) = {!!}


-- -- sub v₂ t₂ (sub v₁ t₁ t) ≡ sub v₁ t₁ (sub v₂ t₂ t)


-- sub-sub :
--   ∀ {Γ A B C}
--     (v₁ : A ∈ Γ)(v₂ : B ∈ subᶜ v₁)
--     (t₁ : Ty (drop v₁) A)(t₂ : Ty (drop v₂) B) (t : Ty Γ C)
--   → sub v₂ t₂ (sub v₁ t₁ t)
--   ≡  let +v₁ = subᶜ-⊆ v₁
--          x = sub (ren-∈ +v₁ v₂) (ren (⊆-drop v₂ +v₁) t₂) t
--          z = sub v₂ t₂ (ren (drop-sub-⊆ v₁) t₁)
--          y : Ty (subᶜ (sub-∈ v₁ v₂)) C
--          y = sub (sub-∈ v₁ v₂) {!!} x

-- -- sub v₂ t₂ (sub v₁ t₁ t) ≡ sub v₁ (sub v₂ t₂ t₁) (sub v₂ t₂ t)
-- --                                   ˇ---> sub the sub

-- -- We need the extra sub, however, v₂ can be in drop v₁ instead of subᶜ v₁

--      in exc→ v₁ v₂ y
-- sub-sub = {!sub-∈!}





