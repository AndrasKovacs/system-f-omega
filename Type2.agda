{-# OPTIONS --without-K #-}

module SystemFOmega.Type2 where

open import Data.Sum renaming (map to smap)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to pmap)
import Function as F
open import Function using (_$_)
open import Data.Empty
open import Data.Unit

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

drop : ∀ {Γ A} → A ∈ Γ → Con -- "drop Γ ⊆ Γ" always true
drop {Γ ▷ _} vz     = Γ
drop {Γ ▷ _} (vs v) = drop v

subᶜ : ∀ {Γ A} → A ∈ Γ → Con
subᶜ {Γ ▷ _} vz     = Γ
subᶜ {Γ ▷ A} (vs v) = subᶜ v ▷ A

drop-sub-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ subᶜ v
drop-sub-⊆ vz     = id
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

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

-- normalization
--------------------------------------------------------------------------------

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

-- Properties
--------------------------------------------------------------------------------

inj₂-inj : ∀ {A B : Set}{x y : B} → ((A ⊎ B) F.∋ inj₂ x) ≡ inj₂ y → x ≡ y
inj₂-inj refl = refl

⊎-conflict : ∀ {A B : Set}{x : A}{y : B} → ((A ⊎ B) F.∋ inj₁ x) ≢ inj₂ y
⊎-conflict ()

-- ∈-eq-ins :
--   ∀ {Γ A} B i (v : A ∈ Γ) → ∈-eq i (ren-∈ (ins-⊆ Γ i B) v) ≡ inj₂ v
-- ∈-eq-ins A iz     vz     = refl
-- ∈-eq-ins A iz     (vs v) = cong (inj₂ F.∘ vs_) (ren-∈-id v)
-- ∈-eq-ins A (is i) vz     = refl
-- ∈-eq-ins A (is i) (vs v) = cong (smap F.id vs_) (∈-eq-ins A i v)

-- mutual
--   sub-ren : ∀ {Γ A B} i (t' : Ty (drop Γ i) B)(t : Ty Γ A) → sub i t' (ren (ins-⊆ Γ i B) t) ≡ t
--   sub-ren i t' (A ⇒ B) = cong₂ _⇒_ (sub-ren i t' A) (sub-ren i t' B)
--   sub-ren i t' (∀' A)  = cong ∀'_ (sub-ren (is i) t' A)
--   sub-ren i t' (ƛ t)   = cong ƛ_  (sub-ren (is i) t' t)
--   sub-ren {B = B} i t' (ne (v , sp))
--     with ∈-eq i (ren-∈ (ins-⊆ _ i B) v) | inspect (∈-eq i) (ren-∈ (ins-⊆ _ i B) v)
--   ... | inj₂ v' | [ eq ] = cong₂ (λ x y → ne (x , y))
--      (inj₂-inj $ trans (sym eq) (∈-eq-ins B i v))
--      (subSp-ren i t' sp)
--   ... | inj₁ refl | [ eq ] with sym $ trans (sym $ ∈-eq-ins B i v) eq
--   ... | ()

--   subSp-ren :
--     ∀ {Γ A B C} i (t' : Ty (drop Γ i) B)(sp : Sp Γ A C) → subSp i t' (renSp (ins-⊆ Γ i B) sp) ≡ sp
--   subSp-ren i t' ε        = refl
--   subSp-ren i t' (x ∷ sp) = cong₂ _∷_ (sub-ren i t' x) (subSp-ren i t' sp)

--------------------------------------------------------------------------------

top-add : ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(t : Ty Γ A) → ren (top {B}) (ren o t) ≡ ren (add o) t
top-add {B = B} o t rewrite ren-∘ (top{B}) o t | id-∘ o = refl

top-keep :
  ∀ {Γ Δ A B}(t : Ty Γ A)(o : Γ ⊆ Δ) → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-keep {B = B} t o rewrite
  ren-∘ (top{B}) o t | ren-∘ (keep o) (top {B}) t | id-∘ o | ∘-id o = refl

--------------------------------------------------------------------------------

-- ∈-eq-ins-comm :
--   ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(i : Ix Γ) {{p : Ins i o}}(v : A ∈ ins Γ i B)
--   → ∈-eq (ren-Ix o i) (ren-∈ (⊆-ins o i) v) ≡ ren-∈-Eq o (∈-eq i v)
-- ∈-eq-ins-comm o        iz     vz     = refl
-- ∈-eq-ins-comm o        iz     (vs v) = refl
-- ∈-eq-ins-comm (add o)  (is i) {{()}} vz
-- ∈-eq-ins-comm (keep o) (is i) vz     = refl
-- ∈-eq-ins-comm (add o)  (is i) {{()}} (vs v)
-- ∈-eq-ins-comm (keep o) (is i) (vs v)
--   with ∈-eq-ins-comm o i v | ∈-eq i v | inspect (∈-eq i) v
-- ... | rec | inj₁ _ | [ eq ] rewrite rec | eq = refl
-- ... | rec | inj₂ _ | [ eq ] rewrite rec | eq = refl

-- drop-⊆-comm' :
--   ∀ {Γ Δ} (o : Γ ⊆ Δ) i {{_ : Ins i o}} →
--   (drop-⊆ Δ (ren-Ix o i) ∘ ⊆-drop o i) ≡ (o ∘ drop-⊆ Γ i)
-- drop-⊆-comm' o        iz     = trans (id-∘ o) (sym (∘-id o))
-- drop-⊆-comm' (keep o) (is i) = cong add (drop-⊆-comm' o i)
-- drop-⊆-comm' (add o)  (is i) {{()}}

-- drop-⊆-comm :
--   ∀ {Γ Δ A} (o : Γ ⊆ Δ) i {{_ : Ins i o}}(t : Ty (drop Γ i) A) →
--   ren (drop-⊆ Δ (ren-Ix o i)) (ren (⊆-drop o i) t) ≡ ren o (ren (drop-⊆ Γ i) t)
-- drop-⊆-comm {Γ}{Δ} o i t rewrite
--   ren-∘ o (drop-⊆ Γ i) t | ren-∘ (drop-⊆ Δ (ren-Ix o i)) (⊆-drop o i) t
--   = cong (λ x → ren x t) (drop-⊆-comm' o i)

-- mutual
--   sub-ren-comm :
--     ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(i : Ix Γ){{p : Ins i o}}(t' : Ty (drop Γ i) A)(t : Ty (ins Γ i A) B)
--     → ren o (sub i t' t) ≡ sub (ren-Ix o i) (ren (⊆-drop o i) t') (ren (⊆-ins o i) t)
--   sub-ren-comm o i t' (A ⇒ B) rewrite sub-ren-comm o i t' A | sub-ren-comm o i t' B = refl
--   sub-ren-comm o i t' (ƛ t)  = cong ƛ_  (sub-ren-comm (keep o) (is i) t' t)
--   sub-ren-comm o i t' (∀' t) = cong ∀'_ (sub-ren-comm (keep o) (is i) t' t)
--   sub-ren-comm o i t' (ne (v , sp)) with
--       ∈-eq (ren-Ix o i) (ren-∈ (⊆-ins o i) v) | ∈-eq-ins-comm o i v | ∈-eq i v | inspect (∈-eq i) v
--   ... | inj₁ refl | p | inj₁ refl | eq rewrite sym $ subSp-ren-comm o i t' sp | drop-⊆-comm  o i t'
--     = appSp-ren-comm o (ren (drop-⊆ _ i) t') (subSp i t' sp)
--   ... | inj₂ v'   | p | inj₂ _    | [ eq ] rewrite eq
--     = cong₂ (λ x y → ne (x , y)) (sym (inj₂-inj p)) (subSp-ren-comm o i t' sp)
--   ... | inj₁ x    | p | inj₂ y    | [ eq ] rewrite eq = ⊥-elim (⊎-conflict p)
--   ... | inj₂ y    | p | inj₁ x    | [ eq ] rewrite eq = ⊥-elim (⊎-conflict (sym p))

--   subSp-ren-comm :
--     ∀ {Γ Δ A B C}(o : Γ ⊆ Δ)(i : Ix Γ){{p : Ins i o}}(t' : Ty (drop Γ i) A)(sp : Sp (ins Γ i A) B C)
--     → renSp o (subSp i t' sp) ≡ subSp (ren-Ix o i) (ren (⊆-drop o i) t') (renSp (⊆-ins o i) sp)
--   subSp-ren-comm o i t' ε        = refl
--   subSp-ren-comm o i t' (t ∷ sp) = cong₂ _∷_ (sub-ren-comm o i t' t ) (subSp-ren-comm o i t' sp)

--   appSp-ren-comm :
--     ∀ {Γ Δ A B} (o : Γ ⊆ Δ) (t : Ty Γ A)(sp : Sp Γ A B)
--     → ren o (appSp t sp) ≡ appSp (ren o t) (renSp o sp)
--   appSp-ren-comm o t     ε         = refl
--   appSp-ren-comm o (ƛ t) (t' ∷ sp) rewrite
--       appSp-ren-comm o (sub iz t' t) sp | sub-ren-comm o iz t' t = refl

